#!/usr/bin/ruby
#
$:.unshift File.dirname(__FILE__) + "/../lib"

require 'pp'
require 'parslet'
require 'parslet/convenience'
require 'open3'

DEBUG = false
COMPILE = ARGV.include? '-compile' 

if COMPILE then
  ARGV.pop
end

module Aaa
  class OhNoesEverythingIsFucked
    def self.method_missing(meth)
      raise "You done fucked, `#{meth}' doesn't exist"
    end
  end

  class Fresh
    @@value = 0
    def self.fresh
      @@value += 1
      "fresh_g#{@@value}"
    end
  end

  class Context
    attr_reader :parent, :ns

    def initialize(parent)
      @parent = parent
      @ns = Hash.new { |h,x|
        if @parent then
          @parent[x]
        else
          OhNoesEverythingIsFucked.send(x)
        end
      }
    end

    def [](x) 
      @ns[x]
    end

    def []=(x, y)
      @ns[x.name] = y
    end

    def close()
      Context.new(self)
    end
  end

  class ExprAST
    def is_expr() true end
    def value() nil end
    def eval(ctx) nil end
    def compile(ctx) "'()" end
  end

  class StmtAST
    attr_accessor :insns

    def is_expr() false end
    def eval(ctx)
      for insn in @insns do
        insn.eval(ctx)
      end
      nil
    end
    def compile(ctx)
      "(begin #{@insns.map {|x| x.compile(ctx)}.join(' ')})"
    end
    def initialize(insns)
      @insns = insns
    end
  end

  class ForAST < StmtAST
    attr_accessor :name, :from, :to

    def initialize(name, from, to, insns)
      super(insns)

      @name = name
      @from = from
      @to = to
    end

    def eval(ctx)
      new_ctx = ctx.close
      for i in @from.eval(ctx)..@to.eval(ctx) do
        new_ctx[@name] = i
        @insns.eval(new_ctx)
      end
      nil
    end

    def compile(ctx)
      new_ctx = ctx.close
      var = Fresh.fresh
      new_ctx[@name] = var
      from = @from.compile(ctx)
      "(for-each (lambda (#{var}) #{@insns.compile(new_ctx)}) (map (lambda (x) (+ #{from} x)) (iota (- #{@to.compile(ctx)} #{from}))))"
    end
  end

  class IfAST < StmtAST
    attr_accessor :cond

    def initialize(cond, insns)
      super(insns)

      @cond = cond
    end

    def eval(ctx)
      if @cond.eval(ctx) then
        @insns.eval(ctx)
      end
      nil
    end

    def compile(ctx)
      "(if #{@cond.compile(ctx)} #{@insns.compile(ctx)} '())"
    end
  end

  class IntLit < ExprAST
    attr_accessor :value
    def initialize(val)
      @value = val
    end
    def eval(ctx)
      @value
    end
    def compile(ctx)
      @value.inspect
    end
  end

  class MathExpr < ExprAST
    attr_accessor :left, :right, :operation
    @@operations = {
        :+ => proc {|x,y,ctx| x.eval(ctx) + y.eval(ctx)},
        :- => proc {|x,y,ctx| x.eval(ctx) - y.eval(ctx)},
        :* => proc {|x,y,ctx| x.eval(ctx) * y.eval(ctx)},
        :^ => proc {|x,y,ctx| x.eval(ctx).pow y.eval(ctx)},
      }

    def initialize(l, r, op)
      @left = l
      @right = r
      @operation = @@operations[op]
      @op = op
    end
    def eval(ctx)
      @operation.call(@left, @right, ctx)
    end
    def compile(ctx)
      "(#{@op} #{@left.compile(ctx)} #{@right.compile(ctx)})"
    end
  end

  class BoolExpr < ExprAST
    attr_accessor :left, :right, :operation
    @@operations = {
        :'==' => proc {|x,y,ctx| x.eval(ctx) == y.eval(ctx)},
        :'<>' => proc {|x,y,ctx| x.eval(ctx) != y.eval(ctx)},
        :'<=' => proc {|x,y,ctx| x.eval(ctx) <= y.eval(ctx)},
        :'>=' => proc {|x,y,ctx| x.eval(ctx) >= y.eval(ctx)},
        :'<'  => proc {|x,y,ctx| x.eval(ctx) < y.eval(ctx)},
        :'>'  => proc {|x,y,ctx| x.eval(ctx) > y.eval(ctx)},
      }
    @@coperations = {
        :'==' => '=',
        :'<>' => '(lambda (x y) (not (= x y)))',
        :'<=' => '<=',
        :'>=' => '>=',
        :'<'  => '<',
        :'>'  => '>',
      }

    def initialize(l, r, op)
      @left = l
      @right = r
      @operation = @@operations[op]
      @op = op
    end
    def eval(ctx)
      @operation.call(@left, @right, ctx)
    end
    def compile(ctx)
      "(#{@@coperations[@op]} #{@left.compile(ctx)} #{@right.compile(ctx)})"
    end
  end

  class VarExpr < ExprAST 
    attr_accessor :name, :value, :expr

    def initialize(name, value = nil, expr = nil)
      @name = name
      @value = value
      @expr = expr
    end
    def eval(ctx)
      if @value then
        c = ctx.close
        c[@name] = @value.eval(ctx)
        @expr.eval(c)
      else
        ctx[@name]
      end
    end
    def compile(ctx)
      if @value then
        c = ctx.close
        var = Fresh.fresh
        c[@name] = var
        "(let ([#{var} #{@value.compile(ctx)}]) #{@expr.compile(c)})"
      else
        ctx[@name]
      end
    end
  end

  class PrintStmt < StmtAST 
    attr_accessor :expr, :kind

    def initialize(expr,  kind)
      @expr = expr
      @kind = kind
    end

    def eval(ctx)
      case kind
      when :print
        p @expr.eval(ctx)
      when :pprint
        pp @expr.eval(ctx)
      when :cprint
        print @expr.eval(ctx).chr
      end
      nil
    end

    def compile(ctx)
      case kind
      when :print
        "(printf \"~s\\n\" #{@expr.eval(ctx)})"
      when :pprint
        "(pretty-print '#{@expr.eval(ctx)})"
      when :cprint
        "(display (integer->char #{@expr.eval(ctx)}))"
      end
    end
  end

  class Parser < Parslet::Parser
    root :statement
    
    rule(:statement) {
      space? >> (sin | sif | sfor | print | expression) >> space?
    }

    rule(:space) {
      match('\s').repeat(1)
    }
    rule(:space?) {
      space.maybe
    }

    rule(:sin) {
      str('let') >> space? >> identifier.as(:name) >> space? >> 
      str('=') >> space? >> expression.as(:value) >> space? >>
      str('in') >> space? >> statement.as(:stmt) >> space?
    }

    rule(:print) {
      (str('pprint') | str('cprint') | str('print')).as(:print) >> space? >> expression.as(:expr) >> space?
    }
    rule(:sif) {
      str('if') >> expression.as(:cond) >> str('then') >> space? >> body.as(:insns) >> str('end') >> space?
    }

    rule (:sfor) {
      str('for') >> space? >>
      identifier.as(:loop_name) >> space? >>
        str('=') >>
        expression.as(:from) >> str('..') >> expression.as(:to) >> 
        str('do') >> body.as(:insns) >> str('end') >> space?
    }

    rule(:expression) {
      space? >> 
        ((str('(') >> expression >> str(')')) | integer | identifier).as(:left) >>
        (boolean | math).maybe >>
      space?
    }

    rule(:body) {
      statement.repeat.as(:body) >> space?
    }
    
    rule(:math) {
      mathop >> expression.as(:right)
    }

    rule(:mathop) {
      space? >> (str('+') | str('-') | str('*') | str('^')).as(:mathop) >> space?
    }

    rule(:integer) {
      ((str('+') | str('-')).maybe >> match("[0-9]").repeat(1)).as(:integer) >> space?
    }

    rule(:boolean) {
      boolop >> expression.as(:right)
    }

    rule(:boolop) {
      space? >> (str("==") | str("<>") | str(">=") | str("<=") | str("<") | str(">")).as(:boolop) >> space?
    }

    rule(:identifier) {
      without_kw(
        match('[a-zA-Z_]') >> match('[a-zA-Z_0-9]').repeat,
        match('[a-zA-Z_0-9]')
      ).as(:identifier) 
    }

    def without_kw(x, alt)
      m_keywords = str('if') | str('for') | str('end') | str('print') | str('cprint') | str('pprint') | str('let') | str('in')
      f = (m_keywords.absent? >> x)
      if alt then
        f | (m_keywords >> alt.repeat(1))
      else
        f
      end
    end
  end

  class Transform
      include Parslet

      attr_reader :t
      def initialize
        @t = Parslet::Transform.new

        t.rule(:identifier => simple(:ident)) { VarExpr.new(ident.to_sym) }
        t.rule(:integer => simple(:int))      { IntLit.new(Integer(int)) }
        t.rule(:body => subtree(:lst))        { StmtAST.new lst }

        t.rule(:name => subtree(:name), :value => subtree(:value), :stmt => subtree(:stmt)) { VarExpr.new(name, value, stmt) }
        t.rule(:cond => subtree(:cond), :insns => subtree(:lst)) { IfAST.new(cond, lst) }
        t.rule(:loop_name => subtree(:name), :from => subtree(:f), :to => subtree(:t), :insns => subtree(:lst)) { ForAST.new(name, f, t, lst) }

        t.rule(:boolop => simple(:op), :right => subtree(:r), :left => subtree(:l)) { BoolExpr.new(l, r, op.to_sym) }
        t.rule(:mathop => simple(:op), :right => subtree(:r), :left => subtree(:l)) { MathExpr.new(l, r, op.to_sym) }

        t.rule(:print => simple(:p), :expr => subtree(:expr)) { PrintStmt.new(expr, p.to_sym) }

        t.rule(:left => subtree(:expr)) { expr }
      end

      def do(tree)
        t.apply(tree)
      end
  end

  class Evaluator
    attr_reader :parser, :transformer, :context

    def initialize()
      @parser = Parser.new
      @transformer = Transform.new
      @context = Context.new nil
    end

    def eval(inp)
      result = @parser.parse input
      result = @transformer.do result
      res.eval @context
    end
  end

  def self.repl()
    STDERR.puts "Badly Designed Language Aaa -- Where mathematics has no place\na-b-c == a-(b-c)"
    parser = Parser.new
    transformer = Transform.new
    context = Context.new(nil)

    tline = ""
    in_count = 0
    loop do
      STDERR.print ">>> " + (' ' * in_count)
      line = gets.chomp
      return if line.empty?

      in_count += line.scan(/\b(if|for)\b/).size
      in_count -= line.scan(/\bend\b/).size

      tline << " " + line
      if in_count > 0 then
        next
      end

      result = parser.parse_with_debug tline
      res = transformer.do result
      pp res if DEBUG
      begin
        res = if COMPILE then
                res.compile(context)
              else 
                res.eval(context)
              end
      rescue => e
        STDERR.print "Error: " + e.message + "\n"
        res = nil
      end
      if res then
        if COMPILE then
          o, s = Open3.capture2("scheme -q", :stdin_data => res)
          print o
        else 
          pp res
        end
      end

      tline = ""
    end
  end
end


Aaa.repl
