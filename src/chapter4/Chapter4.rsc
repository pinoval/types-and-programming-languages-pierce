module chapter4::Chapter4

// Abstract grammar

data Term
	= tmTrue()
	| tmFalse()
	| tmIf(Term t1, Term t2, Term t3)
	| tmZero()
	| tmSucc(Term t1)
	| tmPred(Term t1)
	| tmIsZero(Term t1)
	;
	
bool isNumericalVal(tmZero()) = true;
bool isNumericalVal(tmSucc(t)) = isNumericalVal(t);
default bool isNumericalVal(_) = false;

bool isVal(tmTrue()) = true;
bool isVal(tmFalse()) = true;
bool isVal(Term t) = true
	when isNumerical(t);
default bool isVal(_) = false;

// Small-step evaluator
data Exception = noRuleApplies();

Term eval1(tmIf(tmTrue(), t2, t3)) = t2;          			// E-IFTRUE
Term eval1(tmIf(tmFalse(), t2, t3)) = t3;         			// E-IFFALSE
default Term eval1(tmIf(t1, t2, t3)) = tmIf(t1_, t2, t3)  	// E-IF
	when t1_ := eval1(t1); 
Term eval1(tmSucc(t1)) = tmSucc(t1_)						// E-SUCC	
	when t1_ := eval1(t1);
Term eval1(tmPred(tmZero())) = tmZero();					// E-PREDZERO
Term eval1(tmPred(tmSucc(nv1))) = nv1						// E-PREDSUCC
	when isNumerical(nv1);
default Term eval1(tmPred(t1)) = tmPred(t1_)				// E-PRED
	when t1_ := eval1(t1);
Term eval1(tmIsZero(tmZero())) = tmTrue();					// E-ISZEROZERO
Term eval1(tmIsZero(tmSucc(nv1))) = tmFalse()				// E-ISZEROSUCC
	when isNumericalVal(nv1);
default Term eval1(tmIsZero(t1)) = tmIsZero(t1_)			// E-ISZERO
	when t1_ := eval1(t1);
default Term eval1(_) { throw noRuleApplies(); }

Term eval(Term t){
	try{
		t_ = eval1(t);
		return eval(t_);
	} 
	catch noRuleApplies(): return t;
}

// Examples
public Term t_a = tmIf(tmIsZero(tmSucc(tmZero())), tmZero(), tmSucc(tmZero()));
public Term expected_result_a = tmSucc(tmZero());

public test bool test1() = expected_result_a == eval(t_a);
