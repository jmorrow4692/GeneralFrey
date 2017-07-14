/* --------------------------------------------------------------------------------------
Finding elliptic curves for Section 6

Notes: The code is organized prime by prime in increasing order. The subgroup and j-map
information comes directly from http://www.math.cornell.edu/~zywina/papers/PossibleImages/Equations.txt

 -------------------------------------------------------------------------------------- */

_<t>:=FunctionField(Rationals());


////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
// ell=5
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////

G5:=[
	sub<GL(2,5) | {[-1,0,0,-1], [1,0,0,2]}>,
	sub<GL(2,5) | {[2,0,0,1], [1,0,0,2]}>,
	sub<GL(2,5) | {[0,6,3,0],[2,0,0,2], [1,0,0,-1]}>,
	sub<GL(2,5) | {[2,0,0,1], [1,0,0,2],[0,-1,1,0]}>,
	sub<GL(2,5) | {[-1,0,0,-1], [1,1,0,1], [2,0,0,1]}>,
	sub<GL(2,5) | {[-1,0,0,-1], [1,1,0,1], [1,0,0,2]}>,
	sub<GL(2,5) | {[1,2,1,1],[1,6,3,1], [1,0,0,-1]}>,
	sub<GL(2,5) | {[2,0,0,1],[1,0,0,2],[1,1,0,1]}>,
	sub<GL(2,5) | {[2,0,0,1], [1,0,0,2],[0,-1,1,0],[1,1,1,-1]}>
	];
H5:=[
	[sub<GL(2,5) | {[1,0,0,2]}>, sub<GL(2,5) | {[4,0,0,2]}>],
    	[], [], [],
    	[sub<GL(2,5) | {[2,0,0,1],[1,1,0,1]}>, sub<GL(2,5) | {[2,0,0,4], [1,1,0,1]}>],
    	[sub<GL(2,5) | {[1,0,0,2],[1,1,0,1]}>, sub<GL(2,5) | {[4,0,0,2], [1,1,0,1]}>],
    	[],[],[]
	];
J5:=[
	(t^20+228*t^15+494*t^10-228*t^5+1)^3/(t^5*(t^10-11*t^5-1)^5),
	(t^2+5*t+5)^3*(t^4+5*t^2+25)^3*(t^4+5*t^3+20*t^2+25*t+25)^3/(t^5*(t^4+5*t^3+15*t^2+25*t+25)^5),
	5^4*t^3*(t^2+5*t+10)^3*(2*t^2+5*t+5)^3*(4*t^4+30*t^3+95*t^2+150*t+100)^3/((t^2+5*t+5)^5*(t^4+5*t^3+15*t^2+25*t+25)^5),
	(t+5)^3*(t^2-5)^3*(t^2+5*t+10)^3/(t^2+5*t+5)^5,
	(t^4+228*t^3+494*t^2-228*t+1)^3/(t*(t^2-11*t-1)^5),
	(t^4-12*t^3+14*t^2+12*t+1)^3/(t^5*(t^2-11*t-1)),
	5^3*(t+1)*(2*t+1)^3*(2*t^2-3*t+3)^3/(t^2+t-1)^5,
	5^2*(t^2+10*t+5)^3/t^5,
	t^3*(t^2+5*t+40)
	];
W5:=[
	[-27*(t^20+228*t^15+494*t^10-228*t^5+1), 54*(t^30-522*t^25-10005*t^20-10005*t^10+522*t^5+1)],
	[],[],[],
	[-27*(t^4+228*t^3+494*t^2-228*t+1),54*(t^6-522*t^5-10005*t^4-10005*t^2+522*t+1)],
	[-27*(t^4-12*t^3+14*t^2+12*t+1),54*(t^6-18*t^5+75*t^4+75*t^2+18*t+1)],
	[],[],[]
    	];


	//////////////////////////////////////////////////////////////////////////////////
	// Code for Example 6.3.1
	//////////////////////////////////////////////////////////////////////////////////


_<x> := PolynomialRing(Rationals());
i:=15;
E := WeierstrassModel(EllipticCurveWithjInvariant(Evaluate(J5[8],i)));
assert (Degree(SplittingField(DivisionPolynomial(E,5))) eq 40);
Factorization(DivisionPolynomial(E,5));
f := Factorization(DivisionPolynomial(E,5))[1,1];
N := NumberField(f);
_<a> := PolynomialRing(N);
EN := BaseChange(E,N);
AA := aInvariants(EN);
F := a^2 - Evaluate(a^3 + AA[4]*a + AA[5],N.1);
NF := NumberField(F);
_<b> := PolynomialRing(NF);
EF := BaseChange(EN,NF);
P5 := EF![N.1,NF.1];
assert (Order(P5) eq 5);
KK := AbsoluteField(NF);
PP<X> := PolynomialRing(KK);
[i,Order(P5),ClassNumber(KK)];
PrimeFactors(Numerator(jInvariant(E)));  
EOK:= ChangeRing(IntegralModel(BaseChange(E,KK)),Integers(KK)); 
R,phi:=ResidueClassField(Decomposition(Integers(KK),5)[1][1]); 	
Ep := EllipticCurve(BaseChange(EOK,phi)); 
[IsIrreducible(PP!CyclotomicPolynomial(5)), IsRamified(2,Integers(N)),IsInert(2,Integers(N)),IsSplit(2,Integers(N)), IsSupersingular(Ep)];
[IsRamified(5,Integers(N)),IsInert(5,Integers(N)),IsSplit(5,Integers(N))];
D := Factorization(5*Integers(N))[1,1];
RamificationIndex(D);



////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
// ell=7
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////

G7:=[
	sub<GL(2,7) | {[2,0,0,4], [0,2,1,0],[-1,0,0,-1]}>,
	sub<GL(2,7) | {[3,0,0,1],[1,0,0,3],[0,-1,1,0]}>,
	sub<GL(2,7) | {[-1,0,0,-1],[1,1,0,1],[1,0,0,3]}>,
	sub<GL(2,7) | {[-1,0,0,-1],[1,1,0,1],[3,0,0,1]}>,
	sub<GL(2,7) | {[1,1,0,1],[3,0,0,3],[1,0,0,-1]}>,
	sub<GL(2,7) | {[1,-4,4,1],[1,0,0,-1]}>,
	sub<GL(2,7) | {[3,0,0,1],[1,0,0,3],[1,1,0,1]}>
	];
H7:=[
	[sub<GL(2,7)|{[2,0,0,4], [0,2,1,0]}>], 
    	[],
    	[sub<GL(2,7)|{[1,0,0,3], [1,1,0,1]}>, sub<GL(2,7)|{[-1,0,0,1], [1,0,0,3^2], [1,1,0,1]}>],
    	[sub<GL(2,7)|{[3,0,0,1], [1,1,0,1]}>, sub<GL(2,7)|{[1,0,0,-1], [3^2,0,0,1], [1,1,0,1]}>],
    	[sub<GL(2,7)|{[-1,0,0,1], [3^2,0,0,3^2], [1,1,0,1]}>, sub<GL(2,7)|{[1,0,0,-1], [3^2,0,0,3^2], [1,1,0,1]}>],
    	[],
    	[sub<GL(2,7)|{[3,0,0,1], [1,0,0,3^2], [1,1,0,1]}>, sub<GL(2,7)|{[3^2,0,0,1], [1,0,0,3], [1,1,0,1]}>]
	];
J7:=[
	3^3*5*7^5/2^7,
    	t*(t+1)^3*(t^2-5*t+1)^3*(t^2-5*t+8)^3*(t^4-5*t^3+8*t^2-7*t+7)^3/(t^3-4*t^2+3*t+1)^7,
    	(t^2-t+1)^3*(t^6-11*t^5+30*t^4-15*t^3-10*t^2+5*t+1)^3/((t-1)^7*t^7*(t^3-8*t^2+5*t+1)),
    	(t^2-t+1)^3*(t^6+229*t^5+270*t^4-1695*t^3+1430*t^2-235*t+1)^3/((t-1)*t*(t^3-8*t^2+5*t+1)^7),
    	-(t^2-3*t-3)^3*(t^2-t+1)^3*(3*t^2-9*t+5)^3*(5*t^2-t-1)^3/((t^3-2*t^2-t+1)*(t^3-t^2-2*t+1)^7),
    	64*t^3*(t^2+7)^3*(t^2-7*t+14)^3*(5*t^2-14*t-7)^3/(t^3-7*t^2+7*t+7)^7,
    	(t^2+245*t+2401)^3*(t^2+13*t+49)/t^7
	];
W7:=[
    	[-5^3*7^3,-5^4*7^2*106],
    	[],
	[-27*(t^2-t+1)*(t^6-11*t^5+30*t^4-15*t^3-10*t^2+5*t+1),54*(t^12-18*t^11+117*t^10-354*t^9+570*t^8-486*t^7+273*t^6-222*t^5+174*t^4-46*t^3-15*t^2+6*t+1)],	
	[-27*(t^2-t+1)*(t^6+229*t^5+270*t^4-1695*t^3+1430*t^2-235*t+1),54*(t^12-522*t^11-8955*t^10+37950*t^9-70998*t^8+131562*t^7-253239*t^6+316290*t^5-218058*t^4+80090*t^3-14631*t^2+510*t+1)],
	[-27*7*(t^2-3*t-3)*(t^2-t+1)*(3*t^2-9*t+5)*(5*t^2-t-1),-54*7^2*(t^4-6*t^3+17*t^2-24*t+9)*(3*t^4-4*t^3-5*t^2-2*t-1)*(9*t^4-12*t^3-t^2+8*t-3)],
	[],
	[-27*(t^2+13*t+49)^3*(t^2+245*t+2401), 54*(t^2+13*t+49)^4*(t^4-490*t^3-21609*t^2-235298*t-823543)]
];


	//////////////////////////////////////////////////////////////////////////////////
	// Code for Potential example 6.3.2
	//////////////////////////////////////////////////////////////////////////////////

	
_<x> := PolynomialRing(Rationals());
i:=3;
E := WeierstrassModel(EllipticCurveWithjInvariant(Evaluate(J7[7],i)));
assert (Order(GaloisGroup(DivisionPolynomial(E,7))) eq 126);
f := Factorization(DivisionPolynomial(E,7))[1,1];
N := NumberField(f);
_<a> := PolynomialRing(N);
EN := BaseChange(E,N);
AA := aInvariants(EN);
F := a^2 - Evaluate(a^3 + AA[4]*a + AA[5],N.1);
NF := NumberField(F);
_<b> := PolynomialRing(NF);
EF := BaseChange(EN,NF);
P7 := EF![N.1,NF.1];
assert (Order(P7) eq 7);
KK := AbsoluteField(NF);
PP<X> := PolynomialRing(KK);
EOK:= ChangeRing(IntegralModel(BaseChange(E,KK)),Integers(KK)); 
R,phi:=ResidueClassField(Decomposition(Integers(KK),7)[1][1]); 	
Ep := EllipticCurve(BaseChange(EOK,phi)); 
//Data
E;
KK;
[i,Order(P7)];
Factorization(Numerator(jInvariant(E)));  
Factorization(Denominator(jInvariant(E)));  
[IsIrreducible(PP!CyclotomicPolynomial(7)), IsRamified(2,Integers(KK)),IsInert(2,Integers(KK)),IsSplit(2,Integers(KK)), IsSupersingular(Ep)];
[IsRamified(7,Integers(KK)),IsInert(7,Integers(KK)),IsSplit(7,Integers(KK))];
D := Factorization(7*Integers(KK))[1,1];
RamificationIndex(D);


	//////////////////////////////////////////////////////////////////////////////////
	// Code for Non-example 6.3.3
	// For any choice of i, the code will break since E is super singular mod l
	//////////////////////////////////////////////////////////////////////////////////

	
_<x> := PolynomialRing(Rationals());
I := [i : i in [-100..100] | i ne -20 or i ne 0];
E := WeierstrassModel(QuadraticTwist(EllipticCurve([Evaluate(W7[7,1],i),Evaluate(W7[7,2],i)]),-7));
//Factorization(DivisionPolynomial(E,7));
f := Factorization(DivisionPolynomial(E,7))[1,1];
N := NumberField(f);
_<a> := PolynomialRing(N);
EN := BaseChange(E,N);
AA := aInvariants(EN);
_,B := IsSquare(Evaluate(a^3 + AA[4]*a + AA[5],N.1));
P7 := EN![N.1,B];
KK := AbsoluteField(N);
PP<X> := PolynomialRing(KK);
EOK:= ChangeRing(IntegralModel(BaseChange(E,KK)),Integers(KK)); 
R,phi:=ResidueClassField(Decomposition(Integers(KK),7)[1][1]); 	
Ep := EllipticCurve(BaseChange(EOK,phi)); 


	
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
// ell=13
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////

G13:=[
	sub<GL(2,13) | {[2,0,0,1],[1,1,0,1],[1,0,0,8]}>,
	sub<GL(2,13) | {[8,0,0,1],[1,1,0,1],[1,0,0,2]}>,
	sub<GL(2,13) | {[2,0,0,2],[1,1,0,1],[1,0,0,8]}>,
	sub<GL(2,13) | {[2,0,0,1],[1,1,0,1],[1,0,0,4]}>,
	sub<GL(2,13) | {[4,0,0,1],[1,1,0,1],[1,0,0,2]}>,
	sub<GL(2,13) | {[2,0,0,1],[1,1,0,1],[1,0,0,2]}>,
	sub<GL(2,13) | {[2,0,0,2], [2,0,0,3], [0,-1,1,0], [1,1,-1,1]}>
	];
H13:=[
	[],[],[],
	[sub<GL(2,13) | {[2,0,0,1], [1,0,0,2^4], [1,1,0,1]}>, sub<GL(2,13)| {[2^2,0,0,1], [1,0,0,2^4], [1,1,0,1], [2,0,0,4]}>],
	[sub<GL(2,13) | {[2^4,0,0,1], [1,0,0,2], [1,1,0,1]}>, sub<GL(2,13)| {[2^4,0,0,1], [1,0,0,2^2], [1,1,0,1], [4,0,0,2]}>],
	[], []
	];
P13:=[
	t^12+231*t^11+269*t^10-3160*t^9+6022*t^8-9616*t^7+21880*t^6-34102*t^5+28297*t^4-12455*t^3+2876*t^2-243*t+1,
	t^12-9*t^11+29*t^10-40*t^9+22*t^8-16*t^7+40*t^6-22*t^5-23*t^4+25*t^3-4*t^2-3*t+1,
	(t^4-t^3+2*t^2-9*t+3)*(3*t^4-3*t^3-7*t^2+12*t-4)*(4*t^4-4*t^3-5*t^2+3*t-1),
	t^8+235*t^7+1207*t^6+955*t^5+3840*t^4-955*t^3+1207*t^2-235*t+1,
	t^8-5*t^7+7*t^6-5*t^5+5*t^3+7*t^2+5*t+1,
	t^4+7*t^3+20*t^2+19*t+1
	];
Q13:=[
	t^12-512*t^11-13079*t^10-32300*t^9-104792*t^8-111870*t^7-419368*t^6+111870*t^5-104792*t^4+32300*t^3-13079*t^2+512*t+1,
	t^12-8*t^11+25*t^10-44*t^9+40*t^8+18*t^7-40*t^6-18*t^5+40*t^4+44*t^3+25*t^2+8*t+1
	];
J13:=[
	(t^2-t+1)^3*P13[1]^3/((t-1)*t*(t^3-4*t^2+t+1)^13),
	(t^2-t+1)^3*P13[2]^3/((t-1)^13*t^13*(t^3-4*t^2+t+1)),
	-13^4*(t^2-t+1)^3*P13[3]^3/((t^3-4*t^2+t+1)^13*(5*t^3-7*t^2-8*t+5)),
	(t^4-t^3+5*t^2+t+1)*P13[4]^3/(t*(t^2-3*t-1)^13),
	(t^4-t^3+5*t^2+t+1)*P13[5]^3/(t^13*(t^2-3*t-1)),
	(t^2+5*t+13)*P13[6]^3/t
	];

J13_7:=[ (2^4*5*13^4*17^3)/3^13, -(2^12*5^3*11*13^4)/3^13, (2^18*3^3*13^4*127^3*139^3*157^3*283^3*929)/(5^13*61^13) ];
	
W13:=[
	[],[],[],
    	[-27*(t^4-t^3+5*t^2+t+1)^3*P13[4],54*(t^2+1)*(t^4-t^3+5*t^2+t+1)^4*Q13[1]],
	[-27*(t^4-t^3+5*t^2+t+1)^3*P13[5],54*(t^2+1)*(t^4-t^3+5*t^2+t+1)^4*Q13[2]],
	[],[]
	];


	//////////////////////////////////////////////////////////////////////////////////
	// Code for Example 6.3.4
	//////////////////////////////////////////////////////////////////////////////////

	
_<x> := PolynomialRing(Rationals());
i:=2;
E := WeierstrassModel(EllipticCurveWithjInvariant(Evaluate(J13[2],i)));
//Notation
f1 := Factorization(DivisionPolynomial(E,13))[1,1];
N1 := NumberField(f1);
_<a1> := PolynomialRing(N1);
K1 := NumberField(a1^2 - N1.1);
f2 := Factorization(DivisionPolynomial(E,13))[2,1];
N2 := NumberField(f2);
_<a2> := PolynomialRing(N2);
K2 := NumberField(a2^2 - N2.1);
f3 := Factorization(DivisionPolynomial(E,13))[3,1];
N3 := NumberField(f3);
_<a3> := PolynomialRing(N3);
K3 := NumberField(a3^2 - N3.1);
//For K1
EN1 := BaseChange(E,N1);
AA := aInvariants(EN1);
F1 := a1^2 - Evaluate(a1^3 + AA[4]*a1 + AA[5],N1.1);
NF1 := NumberField(F1);
_<b1> := PolynomialRing(NF1);
EF1 := BaseChange(EN1,NF1);
P131 := EF1![N1.1,NF1.1];
//For K2
EN2 := BaseChange(E,N2);
AA := aInvariants(EN2);
F2 := a2^2 - Evaluate(a2^3 + AA[4]*a2 + AA[5],N2.1);
NF2 := NumberField(F2);
_<b2> := PolynomialRing(NF2);
EF2 := BaseChange(EN2,NF2);
P132 := EF2![N2.1,NF2.1];
//For K3
EN3 := BaseChange(E,N3);
AA := aInvariants(EN3);
F3 := a3^2 - Evaluate(a3^3 + AA[4]*a3 + AA[5],N3.1);
NF3 := NumberField(F3);
_<b3> := PolynomialRing(NF3);
EF3 := BaseChange(EN3,NF3);
P133 := EF3![N3.1,NF3.1];
assert (Order(P131) eq 13) and (Order(P132) eq 13)and(Order(P133) eq 13);
KK := AbsoluteField(NF3);
PP<X> := PolynomialRing(KK);
EOK:= ChangeRing(IntegralModel(BaseChange(E,KK)),Integers(KK)); 
R,phi:=ResidueClassField(Decomposition(Integers(KK),13)[1][1]); 	
Ep := EllipticCurve(BaseChange(EOK,phi)); 
//Data
E;
[i,Order(P133),ClassNumber(KK)];
Factorization(Numerator(jInvariant(E)));  
Factorization(Denominator(jInvariant(E)));  
[IsIrreducible(PP!CyclotomicPolynomial(13)), IsRamified(2,Integers(KK)),IsInert(2,Integers(KK)),IsSplit(2,Integers(KK)), IsSupersingular(Ep)];
[IsRamified(13,Integers(KK)),IsInert(13,Integers(KK)),IsSplit(13,Integers(KK))];
D := Factorization(13*Integers(KK))[1,1];
RamificationIndex(D);


	//////////////////////////////////////////////////////////////////////////////////
	// Code for Example 6.3.5
	//////////////////////////////////////////////////////////////////////////////////


_<x> := PolynomialRing(Rationals());
i:=2;
E := WeierstrassModel(EllipticCurve([Evaluate(W13[5,1],i),Evaluate(W13[5,2],i)]));
//Order(GaloisGroup(DivisionPolynomial(E,13)));
//Factorization(DivisionPolynomial(E,13));
f := Factorization(DivisionPolynomial(E,13))[1,1];
N := NumberField(f);
_<a> := PolynomialRing(N);
EN := BaseChange(E,N);
AA := aInvariants(EN);
_,B := IsSquare(Evaluate(a^3 + AA[4]*a + AA[5],N.1));
P13 := EN![N.1,B];
KK := AbsoluteField(N);
PP<X> := PolynomialRing(KK);
EOK:= ChangeRing(IntegralModel(BaseChange(E,KK)),Integers(KK)); 
R,phi:=ResidueClassField(Decomposition(Integers(KK),13)[1][1]); 	
Ep := EllipticCurve(BaseChange(EOK,phi)); 
//Data
E;
[i,Order(P13),ClassNumber(KK)];
Factorization(Numerator(jInvariant(E)));  
Factorization(Denominator(jInvariant(E)));  
[IsIrreducible(PP!CyclotomicPolynomial(13)), IsRamified(2,Integers(KK)),IsInert(2,Integers(KK)),IsSplit(2,Integers(KK)), IsSupersingular(Ep)];
[IsRamified(13,Integers(KK)),IsInert(13,Integers(KK)),IsSplit(13,Integers(KK))];
D := Factorization(13*Integers(KK))[1,1];
RamificationIndex(D);

	//////////////////////////////////////////////////////////////////////////////////
	// Code for Potential-example 6.3.6 
	//////////////////////////////////////////////////////////////////////////////////


_<x> := PolynomialRing(Rationals());
i:=1;
E := WeierstrassModel(EllipticCurveWithjInvariant(Evaluate(J13[5],i)));
f := Factorization(DivisionPolynomial(E,13))[1,1];
N := NumberField(f);
_<a> := PolynomialRing(N);
EN := BaseChange(E,N);
AA := aInvariants(EN);
F3 := a^2 - Evaluate(a^3 + AA[4]*a + AA[5],N.1);
NF3 := NumberField(F3);
_<b3> := PolynomialRing(NF3);
EF3 := BaseChange(EN,NF3);
P133 := EF3![N.1,NF3.1];
KK := AbsoluteField(NF3);
PP<X> := PolynomialRing(KK);
EOK:= ChangeRing(IntegralModel(BaseChange(E,KK)),Integers(KK)); 
R,phi:=ResidueClassField(Decomposition(Integers(KK),13)[1][1]); 	
Ep := EllipticCurve(BaseChange(EOK,phi)); 
//Data
E;
[i,Order(P133),ClassNumber(KK)];
Factorization(Numerator(jInvariant(E)));  
Factorization(Denominator(jInvariant(E)));  
[IsIrreducible(PP!CyclotomicPolynomial(13)), IsRamified(2,Integers(KK)),IsInert(2,Integers(KK)),IsSplit(2,Integers(KK)), IsSupersingular(Ep)];
[IsRamified(13,Integers(KK)),IsInert(13,Integers(KK)),IsSplit(13,Integers(KK))];
D := Factorization(13*Integers(KK))[1,1];
RamificationIndex(D);


	//////////////////////////////////////////////////////////////////////////////////
	// Code for Non-example 6.3.7. 
	// (The code for the class group will never finish, due to the degree of the number field)
	//////////////////////////////////////////////////////////////////////////////////


_<x> := PolynomialRing(Rationals());
for i in [1..10] do
E := WeierstrassModel(EllipticCurveWithjInvariant(Evaluate(J13[6],i)));
//Order(GaloisGroup(DivisionPolynomial(E,13)));
//Factorization(DivisionPolynomial(E,13));
f := Factorization(DivisionPolynomial(E,13))[1,1];
N := NumberField(f);
_<a> := PolynomialRing(N);
EN := BaseChange(E,N);
AA := aInvariants(EN);
F3 := a^2 - Evaluate(a^3 + AA[4]*a + AA[5],N.1);
NF3 := NumberField(F3);
_<b3> := PolynomialRing(NF3);
EF3 := BaseChange(EN,NF3);
P133 := EF3![N.1,NF3.1];
KK := AbsoluteField(NF3);
PP<X> := PolynomialRing(KK);
EOK:= ChangeRing(IntegralModel(BaseChange(E,KK)),Integers(KK)); 
R,phi:=ResidueClassField(Decomposition(Integers(KK),13)[1][1]); 	
Ep := EllipticCurve(BaseChange(EOK,phi)); 
//Data
E;
[i,Order(P133)];
Factorization(Numerator(jInvariant(E)));  
Factorization(Denominator(jInvariant(E)));  
[IsIrreducible(PP!CyclotomicPolynomial(13)), IsRamified(2,Integers(KK)),IsInert(2,Integers(KK)),IsSplit(2,Integers(KK)), IsSupersingular(Ep)];
[IsRamified(13,Integers(KK)),IsInert(13,Integers(KK)),IsSplit(13,Integers(KK))];
D := Factorization(13*Integers(KK))[1,1];
RamificationIndex(D);
"*********************************";
end for;

////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
// ell=37
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////


G37:=[sub<GL(2,37)| {[2^3,0,0,1], [1,0,0,2], [1,1,0,1]}>,
    sub<GL(2,37)| {[2,0,0,1], [1,0,0,2^3], [1,1,0,1]}>  ];
H37:=[[],[]];
J37:=[-7*11^3, -7*137^3*2083^3];
W37:=[[],[]];


	//////////////////////////////////////////////////////////////////////////////////
	// Code for Potential example 6.3.8
	// (This code for the class group and ramification indices will never finish, due to the 	// degree of the number field)
	//////////////////////////////////////////////////////////////////////////////////


_<x> := PolynomialRing(Rationals());
E := WeierstrassModel(EllipticCurveWithjInvariant(J37[1]));
//Order(GaloisGroup(DivisionPolynomial(E,13)));
F:= Factorization(DivisionPolynomial(E,37));
//Notation
f1 := F[1,1];
N1 := NumberField(f1);
_<a1> := PolynomialRing(N1);
K1 := NumberField(a1^2 - N1.1);
f2 := F[2,1];
N2 := NumberField(f2);
_<a2> := PolynomialRing(N2);
K2 := NumberField(a2^2 - N2.1);
f3 := F[3,1];
N3 := NumberField(f3);
_<a3> := PolynomialRing(N3);
K3 := NumberField(a3^2 - N3.1);
//For K1
EN1 := BaseChange(E,N1);
AA := aInvariants(EN1);
F1 := a1^2 - Evaluate(a1^3 + AA[4]*a1 + AA[5],N1.1);
NF1 := NumberField(F1);
_<b1> := PolynomialRing(NF1);
EF1 := BaseChange(EN1,NF1);
P371 := EF1![N1.1,NF1.1];
//For K2
EN2 := BaseChange(E,N2);
AA := aInvariants(EN2);
F2 := a2^2 - Evaluate(a2^3 + AA[4]*a2 + AA[5],N2.1);
NF2 := NumberField(F2);
_<b2> := PolynomialRing(NF2);
EF2 := BaseChange(EN2,NF2);
P372 := EF2![N2.1,NF2.1];
//For K3
EN3 := BaseChange(E,N3);
AA := aInvariants(EN3);
F3 := a3^2 - Evaluate(a3^3 + AA[4]*a3 + AA[5],N3.1);
NF3 := NumberField(F3);
_<b3> := PolynomialRing(NF3);
EF3 := BaseChange(EN3,NF3);
P373 := EF3![N3.1,NF3.1];
assert (Order(P371) eq 37) and (Order(P372) eq 37)and(Order(P373) eq 37);
//Setup
KK := AbsoluteField(NF3);
PP<X> := PolynomialRing(KK);
EOK:= ChangeRing(IntegralModel(BaseChange(E,KK)),Integers(KK)); 
R,phi:=ResidueClassField(Decomposition(Integers(KK),37)[1][1]); 	
Ep := BaseChange(EOK,phi); 
//Data
E;
[Order(P373),ClassNumber(KK)];
Factorization(Numerator(jInvariant(E)));  
Factorization(Denominator(jInvariant(E)));  
[IsIrreducible(PP!CyclotomicPolynomial(37)), IsRamified(2,Integers(KK)),IsInert(2,Integers(KK)),IsSplit(2,Integers(KK)), #Points(Ep) eq #R + 1];
[IsRamified(37,Integers(KK)),IsInert(37,Integers(KK)),IsSplit(37,Integers(KK))];
D := Factorization(37*Integers(KK))[1,1];
RamificationIndex(D);









