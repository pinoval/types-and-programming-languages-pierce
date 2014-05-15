module chapter7::Chapter7

import List;
import ParseTree;
import IO;
import ValueIO;

// Concrete grammar
lexical Identifier
 = [a-z A-Z] [a-z A-Z 0-9]* !>> [a-z A-Z 0-9];
   

layout LAYOUTLIST
  = LAYOUT* !>> [\t-\n \r \ ] !>> "//" !>> "/*";

lexical LAYOUT
  = [\t-\n \r \ ] 
  ;

start syntax LTerm
	= var: Identifier name
	| abs: "λ"  Identifier name  "." LTerm body
	| app: LTerm t1 LTerm t2
	| par: "(" LTerm t ")"
	;
	
	
alias Binding = value;
alias Context = lrel[str name, Binding binding];
	
// Implode

int name2index(Context ctx, str name) = indexOf([k | <k, _> <- ctx], name);
str index2name(Context ctx, int n) = name
	when l := size(ctx), 
		 <name, _> := ctx[l-n-1];  // Verify this 

Term implode((LTerm) `<Identifier name>`, Context ctx) = tmVar(name2index(ctx, "<name>"), 0);
	
Term implode((LTerm) `λ  <Identifier name>  . <LTerm body>`, Context ctx)
	=  tmAbs("<name>", implode(body, ctx));
	
Term implode((LTerm) `<LTerm t1> <LTerm t2>`, Context ctx)
	= tmApp(implode(t1, ctx), implode(t2, ctx));

Term implode((LTerm) `( <LTerm t> )`, Context ctx) = implode(t, ctx);

Term assignDepth(tmVar(n, _), int count) = tmVar(n, count);
Term assignDepth(tmAbs(x, t), int count) = tmAbs(x, assignDepth(t, count + 1));
Term assignDepth(tmApp(t1, t2), int count) = tmApp(assignDepth(t1, count), assignDepth(t2, count));

Context getContext(LTerm lt){
	Context ctx = [];
	top-down visit(lt){
		case (LTerm) `λ  <Identifier name> . <LTerm _>`: {ctx += [<"<name>", -1>];}
	}
	return ctx;
}

Term toADT(str s) =
	assignDepth(implode(ptree, ctx), 0)
	when ptree := parse(#LTerm, s),
		 ctx := getContext(ptree);
	
// Abstract grammar

data Term
	= tmVar(int n, int ctxLength)
	| tmAbs(str name, Term t)
	| tmApp(Term t1, Term t2)
	;

tuple[Context, str] pickFreshName(Context ctx, str name)
	= name notin ctx ? <(ctx + [<name, -1>]), name> : pickFreshName(ctx, "<name>_");
	
str printTm(Context ctx, tmAbs(x, t1)) =
	"(λ <x_>. <printTm(ctx_, t1)>)"
	when <ctx_, x_> := pickFreshName(ctx, x);

str printTm(Context ctx, tmApp(t1, t2)) =
	"(<printTm(ctx, t1)> <printTm(ctx, t2)>)";
	
str printTm(Context ctx, tmVar(x, n)) =
	(size(ctx) == n) ? index2name(ctx, x) : "[bad index]";

str printTm(Term t) = printTm(ctx, t)
	when ctx := [];

Term termShift(int d, Term t){
	Term walk(int c, tmVar(x, n)) = x >= c? tmVar(x+d, n+d) : tmVar(x, n+d);
	Term walk(int c, tmAbs(x, t1)) = tmAbs(x, walk(c+1, t1));
	Term walk(int c, tmApp(t1, t2)) = tmApp(walk(c, t1), walk(c, t2));
	
	return walk(0, t);
}

Term termSubst(int j, Term s, Term t){
	Term walk(int c, tmVar(x, n)) = x == j+c ? termShift(c, s) : tmVar(x, n);
	Term walk(int c, tmAbs(x, t1)) = tmAbs(x, walk(c+1, t1));
	Term walk(int c, tmApp(t1, t2)) = tmApp(walk(c, t1), walk(c, t2));
	
	return walk(0, t);
}

Term termSubstTop(Term s, Term t) = termShift(-1, termSubst(0, termShift(1, s), t));

// Small-step evalutor

data Exception = noRuleApplies();

bool isVal(Context ctx, tmAbs(_, _)) = true;
default bool isVal(Context ctx, Term t) = false;

Term eval1(Context ctx, t:tmApp(tmAbs(x, t12), v2)) = termSubstTop(v2, t12)
	when isVal(ctx, v2);
Term eval1(Context ctx, t:tmApp(v1, t2)) = tmApp(v1, t2_)
	when isVal(ctx, v1),
		 t2_ := eval1(ctx, t2);
Term eval1(Context ctx, t:tmApp(t1, t2)) = tmApp(t1_, t2)
	when t1_ := eval1(ctx, t1);
default Term eval1(Context ctx, _){
	throw noRuleApplies();
}

Term eval(Context ctx, Term t){
	try{
		Term t_ = eval1(ctx, t);
		return eval(ctx, t_);
	}catch noRuleApplies(): return t;
}


