BoG2Isogeny := function( KerTors, deg )
	////	Sanity checks
	if #KerTors ne 2 then;			error "Error: [BoG2Isogeny] KerTors must have 2 elements which are generators.";	end if;
	if ((deg ne 2) and (deg ne 3)) then;	error "Error: [BoG2Isogeny] Only degree 2 and 3 are implemented";			end if;

	if deg eq 2 then;
		return BoRichelotIsogeny( KerTors cat [&+KerTors] );
	elif deg eq 3 then;
		return Bo3Isogeny( KerTors );
	end if;
end function;

BoG2IsogMap := function( KerTors, deg, Pts : Codomain:=false )
	////	Sanity checks
	if #KerTors ne 2 then;			error "Error: [BoG2IsogMap] KerTors must have 2 elements which are generators.";	end if;
	if ((deg ne 2) and (deg ne 3)) then;	error "Error: [BoG2IsogMap] Only degree 2 and 3 are implemented";			end if;

	if deg eq 2 then;
		J,retuple := BoRichIsogMap( KerTors cat [&+KerTors], Pts );
	elif deg eq 3 then;
		J,retuple := Bo3IsogMap( KerTors, Pts );
	end if;

	if Codomain then;	return J, retuple;
	else			return retuple;
	end if;
end function;

LongG2Isogeny := function( KerTors, deg )
	pA := Factorisation( deg )[1,1];
	eA := Factorisation( deg )[1,2];
	////	Sanity checks
	if #KerTors ne 2 then;			error "Error: [LongG2Isogeny] KerTors must have 2 elements which are generators.";	end if;
	if ((pA ne 2) and (pA ne 3)) then;	error "Error: [LongG2Isogeny] Only degree 2 and 3 are implemented";			end if;

	for ind in [1..eA] do;
		J, KerTors := BoG2IsogMap( [pA^(eA-ind)*KerTors[jnd] : jnd in [1,2] ], pA, KerTors : Codomain:=true );
	end for;
	return Curve(J);
end function;

EvaluateLongG2Isogeny := function( KerTors, deg, PList : Codomain:=false )
	pA := Factorisation( deg )[1,1];
	eA := Factorisation( deg )[1,2];
	////	Sanity checks
	if #KerTors ne 2 then;			error "Error: [EvaluateLongG2Isogeny] KerTors must have 2 elements which are generators.";	end if;
	if ((pA ne 2) and (pA ne 3)) then;	error "Error: [EvaluateLongG2Isogeny] Only degree 2 and 3 are implemented";			end if;
	
	Points := KerTors cat PList;
	for ind in [1..eA] do;
		J, Points := BoG2IsogMap( [pA^(eA-ind)*Points[jnd] : jnd in [1,2] ], pA, Points : Codomain:=true );
	end for;

	retuple := Remove(Points,1);	Remove(~retuple,1);	////	Removing the kernel points
	
	if Codomain then;	return J, retuple;
	else			return retuple;
	end if;
end function;
