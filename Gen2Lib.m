Gen2_IsSupersingular_SMALL := function ( J )
	p := Characteristic(BaseRing(J));
	OrdJ := Order(J);
	if OrdJ eq (p+1)^4 then			return true;
	elif OrdJ eq (p-1)^4 then		return true;
	elif OrdJ eq (p+1)^2*(p-1)^2 then	return true;
	end if;
	return false;
end function;

Gen2_IsSupersingular := function ( J )
	K := BaseRing(J);
	p := Characteristic(K);
	O := [(p-1)^2, p^2-1, (p+1)^2];
	for ind in [1..10] do
		P := Random(J);
		if not &or[O[jnd]*P ne J!0 : jnd in [1,2,3]] then
			return false;
		end if;
	end for;
	return true;
end function;

IsIsogenous := function ( C1, C2 )
	O1 := Evaluate(LPolynomial(C1),1);
	O2 := Evaluate(LPolynomial(C2),1);
	if O1 eq O2 then; 	return true;
	else			return false;
	end if;
end function;

CreateCurve_RandomWalk := function ( K )
	_<x> := PolynomialRing(K);
	p := Characteristic(K);
	if IsSupersingular(EllipticCurve(x^3+1)) then; H := HyperellipticCurve(x^6+1); J := Jacobian(H); end if;
	if not Gen2_IsSupersingular( J ) then
		"VOOPSIE!";
		return 0;
	end if;

	NumIter := Ceiling( Log(2, Characteristic(K)) );
	"Number of iterations:",NumIter;
        for i in [1..NumIter] do
		NB := RichelotIsogenousSurfaces(J);
		repeat
			J := NB[1+Random(#NB-1)];
		until Category(J) eq JacHyp;
        end for;
        return Curve(J);
end function;

MumfordToPT := function ( D )
	J := Parent(D);
	C := Curve(J);

	u := D[1]; v := D[2];
	xPs := Roots(u);
	if IsEmpty(xPs) then
		R<x> := Parent(u);
		K := BaseRing(R);
		K := ext<K|2>;
		R<x> := PolynomialRing(K);
		C := BaseChange(C,K);
		u := R!u; v := R!v;
		xPs := Roots(u);
	end if;

	yPs := [ Evaluate(v,xs[1]) : xs in xPs ];
	Ps := [C![xPs[ind,1],yPs[ind]] : ind in [1..#xPs]];
	return Ps;
end function;

MumfordToPT_NoBaseChange := function ( D )
        J := Parent(D);
        C := Curve(J);

        u := D[1]; v := D[2];
        xPs := Roots(u);
        yPs := [ Evaluate(v,xs[1]) : xs in xPs ];
        Ps := [C![xPs[ind,1],yPs[ind]] : ind in [1..#xPs]];

        return Ps;
end function;

PTToMumford := function ( P, Q )
	C := Curve(P);
	f,g := HyperellipticPolynomials(C);
	if Degree(f) eq 5 then
		J := Jacobian(C);
		inf := PointsAtInfinity(C)[1];
		return J![P, inf]+J![Q, inf];
	elif Degree(f) eq 6 then
		J := Jacobian(C);
		return J![C!P,-C!Q];
	else
		"PTToMumford: Weird degree!!";
	end if;
end function;

GetJacobianOrder := function ( C )
	LPol := LPolynomial(C);
	return Evaluate(LPol,1);
end function;

GetSSOrder := function ( J )
	p := Characteristic(BaseRing(J));
	P := Random(J);
	if (p+1)*P eq J!0 then
		return (p+1)^4;
	elif (p-1)*P eq J!0 then
		return (p-1)^4;
	else
		error "GetSSOrder: What other orders are there?", J;
	end if;
end function;

GetCycleOrder := function ( J )
	p := Characteristic(BaseRing(J));
	P := Random(J);
	if (p+1)*P eq J!0 then
		return (p+1);
	elif (p-1)*P eq J!0 then
		return (p-1);
	else
		error "GetSSOrder: What other orders are there?";
	end if;
end function;

TestOrder := function( P, p, e )
	J := Parent(P);
	if (Power(p,e-1)*P ne J!0) and (Power(p,e)*P eq J!0) then
		return true;
	end if;
	return false;
end function;

FindPrime := function ( NumBits )
        TwoPow := Ceiling(NumBits/2);
        ThreePow := Ceiling(NumBits/2/Log(2,3));
        PrimeList := PrimesUpTo(500);
        for ind in [1..5] do
                for f in PrimeList do
                        p := Power(2,TwoPow)*Power(3,ThreePow)*f - 1;
                        if IsPrime(p) then return p; end if;
                end for;
                TwoPow := TwoPow + 1;
        end for;
        return 0;
end function;

IsLinearlyIndependent := function( P, PList, pA, eA )
	MakeOrderp := Power(pA,eA-1);
	if #PList eq 1 then
		B := MakeOrderp*P;
		A := MakeOrderp*PList[1];
		for ind in [1..pA] do;
			if B eq ind*A then;	return false;	end if;
		end for;
		return true;
	elif #PList eq 2 then
		C := MakeOrderp*P;
		A := MakeOrderp*PList[1];
		B := MakeOrderp*PList[2];
		for ind in [1..pA] do; for jnd in [1..pA] do;
			if C eq ind*A+jnd*B then;	return false;	end if;
		end for; end for;
		return true;
	elif #PList eq 3 then
		D := MakeOrderp*P;
		A := MakeOrderp*PList[1];
		B := MakeOrderp*PList[2];
		C := MakeOrderp*PList[3];
		for ind in [1..pA] do; for jnd in [1..pA] do; for knd in [1..pA] do;
			if D eq ind*A+jnd*B+knd*C then;	return false;	end if;
		end for; end for; end for;
		return true;
	else
		return false;
	end if;
end function;

GetSIDHGenerators := function ( J : ComputeBPts:=true, verbose:=true )
	p := Characteristic(BaseRing(J));
	OrdJ := GetCycleOrder(J);
	OrdJ_fact := Factorisation(OrdJ);
	pA := OrdJ_fact[1,1];	eA := OrdJ_fact[1,2];
	pB := OrdJ_fact[2,1];	eB := OrdJ_fact[2,2];
	AOrd := Power(pA,eA);
	BOrd := Power(pB,eB);
	ACofac := Integers()!(OrdJ/AOrd);
	BCofac := Integers()!(OrdJ/BOrd);

	// Generating A points
	repeat P := ACofac*Random(J);	until TestOrder(P,pA,eA);
	A_Pts := [P];
	if verbose then; "A_Pts: Found 1 point."; end if;
	repeat
		repeat P := ACofac*Random(J);	until TestOrder(P,pA,eA);
		if IsLinearlyIndependent( P, A_Pts, pA, eA ) then
			Append(~A_Pts, P);
			if verbose then; "A_Pts: Found",#A_Pts,"points."; end if;
		end if;
	until #A_Pts eq 4;

	// Generating B points
	if ComputeBPts then
		repeat P := BCofac*Random(J);	until TestOrder(P,pB,eB);
		B_Pts := [P];
		if verbose then; "B_Pts: Found 1 point."; end if;
		repeat
			repeat P := BCofac*Random(J);	until TestOrder(P,pB,eB);
			if IsLinearlyIndependent( P, B_Pts, pB, eB ) then
				Append(~B_Pts, P);
				if verbose then; "B_Pts: Found",#B_Pts,"points."; end if;
			end if;
		until #B_Pts eq 4;
	else
		B_Pts := [];
	end if;
	return A_Pts, B_Pts;
end function;

CheckOrder := function( n, p, e )
	k := Parent(n);
	return ( n^Power(p,e) eq k!1 ) and ( n^Power(p,e-1) ne k!1 );
end function;

GetSabrinaGenerators := function( A_Pts, pA, eA )

	n := Power(pA,eA);
	e12 := WeilPairing( A_Pts[1], A_Pts[2], n );
	e13 := WeilPairing( A_Pts[1], A_Pts[3], n );
	e14 := WeilPairing( A_Pts[1], A_Pts[4], n );
	e23 := WeilPairing( A_Pts[2], A_Pts[3], n );
	e24 := WeilPairing( A_Pts[2], A_Pts[4], n );
	e34 := WeilPairing( A_Pts[3], A_Pts[4], n );

	k13 := Log(e12,e13);
	k14 := Log(e12,e14);
	k23 := Log(e12,e23);
	k24 := Log(e12,e24);
	k34 := Log(e12,e34);

	//  Equations that we need to solve:
	//  a1*b2-a2*b1 + k13*(a1*b3-a3*b1) + k14*(a1*b4-a4*b1) + k23*(a2*b3-a3*b2) + k24*(a2*b4-a4*b2) + k34*(a3*b4-a4*b3) = 0 mod 2^n
	//  c1*d2-c2*d1 + k13*(c1*d3-c3*d1) + k14*(c1*d4-c4*d1) + k23*(c2*d3-c3*d2) + k24*(c2*d4-c4*d2) + k34*(c3*d4-c4*d3) = 0 mod 2^n
	//  a1*c2-a2*c1 + k13*(a1*c3-a3*c1) + k14*(a1*c4-a4*c1) + k23*(a2*c3-a3*c2) + k24*(a2*c4-a4*c2) + k34*(a3*c4-a4*c3) = 1 mod 2
	//  b1*d2-b2*d1 + k13*(b1*d3-b3*d1) + k14*(b1*d4-b4*d1) + k23*(b2*d3-b3*d2) + k24*(b2*d4-b4*d2) + k34*(b3*d4-b4*d3) = 1 mod 2
	//
	//  Set a2=a3=a4=0, a1=1
	//  b2 + k13*(b3) + k14*(b4) = 0 mod 2^n    ==>    Pick b3, b4 to be random odds, and set b2 accordingly
	//  c2 + k13*(c3) + k14*(c4) = 1 mod 2      ==>    Pick c3, c4 to be random odds, and set c2 accordingly
	//  Set d2 = 1, d3=d4=0
	//  c1 - c2*d1 + k13*(-c3*d1) + k14*(-c4*d1) + k23*(-c3) + k24*(-c4) = 0 mod 2^n
	//  b1 - b2*d1 + k13*(b3*d1) + k14*(b4*d1) + k23*(-b3) + k24*(-b4) = 1 mod 2

	a := [ 1, 0, 0, 0 ];
	repeat  b3 := Random(n);	until b3 mod 2 eq 1;
	repeat  b4 := Random(n);	until b4 mod 2 eq 1;
	b2 := -k13*b3 - k14*b4;
	repeat  c3 := Random(n);	until c3 mod 2 eq 1;
	repeat  c4 := Random(n);	until c4 mod 2 eq 1;
	if ((k13*c3 + k14*c4) mod 2) eq 0 then
		repeat c2 := Random(n);	until c2 mod 2 eq 1;
	else
		repeat c2 := Random(n);	until c2 mod 2 eq 0;
	end if;
	d := [ Random(n), 1, 0, 0 ];
	c1 := c2*d[1] + k13*(c3*d[1]) + k14*(c4*d[1]) + k23*(c3) + k24*(c4);
	if (-b2*d[1] + k13*(b3*d[1]) + k14*(b4*d[1]) + k23*(-b3) + k24*(-b4)) mod 2 eq 0 then
		repeat b1 := Random(n); until b1 mod 2 eq 1;
	else
		repeat b1 := Random(n); until b1 mod 2 eq 0;
	end if;

	b := [ b1, b2, b3, b4 ];
	c := [ c1, c2, c3, c4 ];
	
	P1 := &+[ a[ind]*A_Pts[ind] : ind in [1..4] ];
	P2 := &+[ b[ind]*A_Pts[ind] : ind in [1..4] ];
	P3 := &+[ c[ind]*A_Pts[ind] : ind in [1..4] ];
	P4 := &+[ d[ind]*A_Pts[ind] : ind in [1..4] ];

	return [P1,P2,P3,P4];

end function;

PrintSIDHGenerators := procedure( n, AP, BP )
	SetColumns(0);
	printf "J%o_APts := [  J%o![ %o,\n", n, n, AP[1,1];
	printf "                + %o ],\n", AP[1,2];
	printf "              J%o![ %o,\n", n, AP[2,1];
	printf "                + %o ],\n", AP[2,2];
	printf "              J%o![ %o,\n", n, AP[3,1];
	printf "                + %o ],\n", AP[3,2];
	printf "              J%o![ %o,\n", n, AP[4,1];
	printf "                + %o ] ];\n", AP[4,2];
	printf "J%o_BPts := [  J%o![ %o,\n", n, n, BP[1,1];
	printf "                + %o ],\n", BP[1,2];
	printf "              J%o![ %o,\n", n, BP[2,1];
	printf "                + %o ],\n", BP[2,2];
	printf "              J%o![ %o,\n", n, BP[3,1];
	printf "                + %o ],\n", BP[3,2];
	printf "              J%o![ %o,\n", n, BP[4,1];
	printf "                + %o ] ];\n", BP[4,2];
end procedure;

GetTorsSubgroup := function ( J, ell )
	Tors := {@@};
	JOrd := GetCycleOrder(J);
	CoFact := Integers()!(JOrd/ell);
	repeat
		P := CoFact*Random(J);
		Include( ~Tors, P );
	until #Tors eq ell^4;
	return Tors;
end function;

GetSSPointOrder := function( P )
	J := Parent(P);
	p := Characteristic(BaseRing(J));
	FactorP1 := Factorisation(p+1);
	if #FactorP1 ne 3 then;	"Abelian surface may not be supersingular. Or prime chosen in a weird way.";	end if;
	CoFacExp := [0,0,0];
	for ind in [1..3] do
		for jnd in [0..FactorP1[ind,2]] do
			t := (p+1)/(FactorP1[ind,1]^jnd);
			D := Integers()!t*P;
			if D ne J!0 then
				CoFacExp[ind] := jnd-1;
				break;
			end if;
		end for;
	end for;
	return &*[ FactorP1[ind,1]^( FactorP1[ind,2] - CoFacExp[ind] ) : ind in [1,2,3] ];
end function;

////    p-adic expression to decimal integer
PListToDec := function( a, p )
        val := 0;
        if #a eq 0 then;        return val;     end if;
        for i in [0..#a-1] do;  val +:= (p^i)*Integers()!a[i+1];        end for;
        return val;
end function;

////    Use SPH to find discrete logarithms
SPH_same_prime := function( X, P, prime, pow )
        l := [];
        m := [];
        n := [];
        o := [];
        for i in [1..pow] do
                A := prime^(pow-i)*(X - PListToDec(l,prime)*P[1] - PListToDec(m,prime)*P[2] - PListToDec(n,prime)*P[3] - PListToDec(o,prime)*P[4]);
                Q := [ prime^(pow-1)*P[ind] : ind in [1..4] ];
                for a in [0,prime-1] do
                for b in [0,prime-1] do
                for c in [0,prime-1] do
                for d in [0,prime-1] do
                        if A eq a*Q[1]+b*Q[2]+c*Q[3]+d*Q[4] then
                                Append( ~l, a );
                                Append( ~m, b );
                                Append( ~n, c );
                                Append( ~o, d );
                                break;
                        end if;
                end for; end for; end for; end for;
        end for;
        return [PListToDec(l,prime), PListToDec(m,prime), PListToDec(n,prime), PListToDec(o,prime)];
end function;
