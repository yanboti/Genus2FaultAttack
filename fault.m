load "Gen2Lib.m";
load "2RichLib.m";
load "3RichLib.m";
load "Gen2IsogLib.m";

SetColumns(0);

////    p-adic expression to decimal integer
PListToDec := function( a, p )
        val := 0;
        if #a eq 0 then;        return val;     end if;
        for i in [0..#a-1] do;  val +:= (p^i)*Integers()!a[i+1];        end for;
        return val;
end function;


Is_2n2n_Subgroup := function( Ker, n )
        J := Parent(Ker[1]);
        //  Checking number of generators
        if #Ker ne 2 then;                                              return false, 1;        end if;
        //  Checking order of generators
        if (Power(2,n)*Ker[1] ne J!0) then;                             return false, 2;        end if;
        if (Power(2,n)*Ker[2] ne J!0) then;                             return false, 3;        end if;
        if (Power(2,n-1)*Ker[1] eq J!0) then;                           return false, 4;        end if;
        if (Power(2,n-1)*Ker[2] eq J!0) then;                           return false, 5;        end if;
        //  Checking linear independence
        if (Power(2,n-1)*Ker[1] eq Power(2,n-1)*Ker[2]) then;           return false, 6;        end if;
        //  Checking Weil pairing
        if WeilPairing( Ker[1], Ker[2], Power(2,n) ) ne 1 then;         return false, 7;        end if;

        return true;
end function;

Is_3n3n_Subgroup := function( Ker, n )
        J := Parent(Ker[1]);
        //  Checking number of generators
        if #Ker ne 2 then;                                              return false, 1;        end if;
        //  Checking order of generators
        if (Power(3,n)*Ker[1] ne J!0) then;                             return false, 2;        end if;
        if (Power(3,n)*Ker[2] ne J!0) then;                             return false, 3;        end if;
        if (Power(3,n-1)*Ker[1] eq J!0) then;                           return false, 4;        end if;
        if (Power(3,n-1)*Ker[2] eq J!0) then;                           return false, 5;        end if;
        //  Checking linear independence
        if (Power(3,n-1)*Ker[1] eq Power(3,n-1)*Ker[2]) then;           return false, 6;        end if;
        if (Power(3,n-1)*Ker[1] eq 2*Power(3,n-1)*Ker[2]) then;         return false, 7;        end if;
        //  Checking Weil pairing
        if WeilPairing( Ker[1], Ker[2], Power(3,n) ) ne 1 then;         return false, 8;        end if;

        return true;
end function;

////	This function simulates a fault injection.
////	It does so by randomising coefficients of the polynomials
////	in the Mumford representation.
////	We can write the Mumford representation as [x^2+(a*u+b)*x+(c*u+d),(e*u+f)*x+(g*u+h)]
////	This function injects a fault in *a*, and computes the neccesary e,f,g,h to make it
////	a point on the Jacobian.
FaultPointAtV := function( P )
	J := Parent(P);
	H := Curve(J);
	R<x> := Parent(P[1]);
	K<u> := BaseRing(R);
	k := PrimeField(K);

	v := Reverse(&cat(Remove([ ElementToSequence(ind) : ind in Coefficients(P[1]) ],3)));
	v[1] := Random(k);

	f := x^2+(v[1]*u+v[2])*x+(v[3]*u+v[4]);
	r := Roots(f);
	if #r ne 2 then;
		print "Fault injection failed: No roots.";
		return 0;
	end if;
	Q1_x := r[1,1];
	Q2_x := r[2,1];
	f,_ := HyperellipticPolynomials(H);
	IsSq1, Q1_y := IsSquare(Evaluate(f,Q1_x));
	IsSq2, Q2_y := IsSquare(Evaluate(f,Q2_x));
	if not(IsSq1 and IsSq2) then
		print "Fault injection failed: No square roots.";
		return 0;
	end if;
	
	Q1 := H![Q1_x,Q1_y];
	Q2 := H![Q2_x,Q2_y];
	return PTToMumford(Q1,Q2);
end function;

////	This function simulates a fault injection.
////	It does so by flipping certain bits of coefficients of 
////	the polynomials in the Mumford representation.
////	We can write the Mumford representation as [x^2+(a*u+b)*x+(c*u+d),(e*u+f)*x+(g*u+h)]
////	BitsToFlip is a tuple of 4 tuples. Each tuple contains the bits that 
////	are to be flipped in coefficients of the first polynomial.
FaultPointAtV_bitflips := function( P, BitsToFlip )
	J := Parent(P);
	H := Curve(J);
	R<x> := Parent(P[1]);
	K<u> := BaseRing(R);
	k := PrimeField(K);

	v := Reverse(&cat(Remove([ ElementToSequence(ind) : ind in Coefficients(P[1]) ],3)));
	for ind in [1..4] do
		if IsEmpty(BitsToFlip[ind]) then;	continue;	end if;
		temp := Intseq(Integers()!v[ind],2);
		for jnd in BitsToFlip[ind] do
			temp[jnd] := (temp[jnd]+1) mod 2;
		end for;
		v[ind] := PListToDec(temp,2);
	end for;

	f := x^2+(v[1]*u+v[2])*x+(v[3]*u+v[4]);
	r := Roots(f);
	if #r ne 2 then;
		print "Fault injection failed: No roots.";
		return 0;
	end if;
	Q1_x := r[1,1];
	Q2_x := r[2,1];
	f,_ := HyperellipticPolynomials(H);
	IsSq1, Q1_y := IsSquare(Evaluate(f,Q1_x));
	IsSq2, Q2_y := IsSquare(Evaluate(f,Q2_x));
	if not(IsSq1 and IsSq2) then
		print "Fault injection failed: No square roots.";
		return 0;
	end if;
	
	Q1 := H![Q1_x,Q1_y];
	Q2 := H![Q2_x,Q2_y];
	return PTToMumford(Q1,Q2);
end function;


////////////////////////////////////////////////
////////	THIS NEEDS DEBUGGING	////////
////////////////////////////////////////////////
////	This function simulates a fault injection.
////	It does so by randomising coefficients of the polynomials
////	in the Mumford representation.
////	We can write the Mumford representation as [x^2+(a*u+b)*x+(c*u+d),(e*u+f)*x+(g*u+h)]
////	The optional input "model" has 8 bits in an array: [a,b,c,d,e,f,g,h].
////	Each bit in "model" indicates if a fault is present. 
FaultPoint := function( P : model:=[true,false,false,false,false,false,false,false])
	J := Parent(P);
	R<x> := Parent(P[1]);
	K<u> := BaseRing(R);
	k := PrimeField(K);

	v := Reverse(&cat(Remove([ ElementToSequence(ind) : ind in Coefficients(P[1]) ],3)));
	w := Reverse(&cat([ ElementToSequence(ind) : ind in Coefficients(P[2]) ]));

	assert #model eq 8;
	for ind in [1..4] do
		if model[ind] then
			v[ind] := Random(k);
		end if;
		if model[ind+4] then
			w[ind] := Random(k);
		end if;
	end for;
	return J![ x^2+(v[1]*u+v[2])*x+(v[3]*u+v[4]),(w[1]*u+w[2])*x+(w[3]*u+w[4]) ];
end function;


p := 24554940634497023;
eA := 25;
eB := 16;
 f := 17;
K<u> := GF(p^2);
R<x>:=PolynomialRing(K);
	
C_1 := HyperellipticCurve( (13274801814165018*K.1 + 7650378754263570)*x^6
			+ (10468506766346375*K.1 + 2679228971360392)*x^5
			+ (21625069997560015*K.1 + 7231499835169234)*x^4
			+ (23300095300354839*K.1 + 20580385459668126)*x^3
			+ (5065415789788622*K.1 + 11531147184110145)*x^2
			+ (23889770567634828*K.1 + 10123228279895739)*x
			+ (7551381872957476*K.1 + 22216347959038604) );
J_1 := Jacobian( C_1 );
A_Pts := [	J_1![ x^2 + (4417785193388650*K.1 + 10076052864162644)*x + 12041254618535425*K.1 + 10192091337102567,
		(24385328339892224*K.1 + 9236700539501717)*x + 4458267451255414*K.1 + 16274884916448363 ],
		J_1![ x^2 + (17170593898342698*K.1 + 20580696788515843)*x + 2149819620376687*K.1 + 15197817484526988,
		(7369424147980847*K.1 + 16206802756214115)*x + 22370664897838533*K.1 + 12982818204276925 ],
		J_1![ x^2 + (1102662549884223*K.1 + 22952351396622855)*x + 954543490269934*K.1 + 11283909318197813,
		(24323808182813779*K.1 + 13576805264383338)*x + 3753545492981554*K.1 + 13655611788346224 ],
		J_1![ x^2 + (10210902488262852*K.1 + 17792958613359860)*x + 6069917482154694*K.1 + 11009119457245319,
		(8215865743434535*K.1 + 4105760955503058)*x + 18899622157668356*K.1 + 15950580569902151 ] ];
B_Pts := [	J_1![ x^2 + (12953871615244519*K.1 + 22303130521897071)*x + 11330541243603715*K.1 + 7550900602507706,
		(958718867290920*K.1 + 22093607943314534)*x + 12673583884239515*K.1 + 8999270162350091 ],
		J_1![ x^2 + (13739479351716499*K.1 + 3840642126050431)*x + 14309413018251915*K.1 + 2813481264255110,
		(21034771983702255*K.1 + 10961571210305614)*x + 12579119427435094*K.1 + 9111138881629886 ],
		J_1![ x^2 + (5914870561884695*K.1 + 2817106494271049)*x + 22444382103237101*K.1 + 10291793597027096,
		(11453781406630774*K.1 + 9579920014940796)*x + 17855555611944011*K.1 + 9940294153703786 ],
		J_1![ x^2 + (1897784672027290*K.1 + 255274022390089)*x + 14570908638051639*K.1 + 6390336138632822,
		(15700980523244027*K.1 + 8335493964640161)*x + 10132420138422505*K.1 + 10791662765489588 ] ];

a := [ 11050732, 20781979, 15124175, 9228661 ];

KerA := [ a[1]*A_Pts[1]+a[2]*A_Pts[2], a[3]*A_Pts[3]+a[4]*A_Pts[4] ];

newB_Pts := B_Pts;
newB_Pts[1] := FaultPointAtV_bitflips (B_Pts[1],[[33,34,35,36,37,38,39,40],[],[],[]]);
newB_Pts[2] := FaultPointAtV_bitflips (B_Pts[2],[[48,49,50,51,52,53],[],[],[]]);
newB_Pts[3] := FaultPointAtV_bitflips (B_Pts[3],[[21,22,23,24,25],[],[],[]]);
newB_Pts[4] := FaultPointAtV_bitflips (B_Pts[4],[[1,2,3,5,8,13,21],[],[],[]]);
JA, MappednewBPts := EvaluateLongG2Isogeny(KerA,2^eA,newB_Pts:Codomain:=true);

ZPts := [ 3^eB*f*Pind : Pind in  MappednewBPts ];

WeilPairing(ZPts[1],ZPts[2],2^eA) eq 1 and 2^(eA-1)*ZPts[1] ne 2^(eA-1)*ZPts[2];
WeilPairing(ZPts[1],ZPts[3],2^eA) eq 1 and 2^(eA-1)*ZPts[1] ne 2^(eA-1)*ZPts[3];
WeilPairing(ZPts[1],ZPts[4],2^eA) eq 1 and 2^(eA-1)*ZPts[1] ne 2^(eA-1)*ZPts[4];
WeilPairing(ZPts[2],ZPts[3],2^eA) eq 1 and 2^(eA-1)*ZPts[2] ne 2^(eA-1)*ZPts[3];
WeilPairing(ZPts[2],ZPts[4],2^eA) eq 1 and 2^(eA-1)*ZPts[2] ne 2^(eA-1)*ZPts[4];
WeilPairing(ZPts[3],ZPts[4],2^eA) eq 1 and 2^(eA-1)*ZPts[3] ne 2^(eA-1)*ZPts[4];


print "Target G2-invariant: ";
G2Invariants(C_1);

print "Candidate G2-invariants: "
G2Invariants(LongG2Isogeny([ZPts[1],ZPts[2]],2^eA));
G2Invariants(LongG2Isogeny([ZPts[1],ZPts[3]],2^eA));
G2Invariants(LongG2Isogeny([ZPts[2],ZPts[4]],2^eA));
G2Invariants(LongG2Isogeny([ZPts[3],ZPts[4]],2^eA));
