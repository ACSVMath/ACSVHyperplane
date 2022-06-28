# Create kth elementary vector
eVect := proc(k,d) local v;
  v := Transpose(ZeroVector(d));
  v[k] := 1;
  return convert(v,list):
end:

##########################################################################################################
# Calculates contributing singularities of F = G/H in direction r, assuming G and H are relatively prime and 
# H splits into linear factors *over Q*.
#
# INPUT: 		G - numerator of F
#				H - denominator of F
#				r - direction, containing *positive integers*
#			 vars - ordered list of variables, same length as r
#			    u - variable (not contained in vars)
#
# OUTPUT:       Set whose elements encode contributing singularities of F
#				Each element of the set is a list with three elements: L, N, and S 
#					- L is a list [P,Q,a] such that the contributing point has jth coordinate equal 
#						Q[j]/P' when u = closest root of P to floating point number a
#					- N gives numerical approximations for the point's coordinates
#					- S gives the indices of the linear factors defining the flat containing the point
###########################################################################################################
contribSing := proc(G,H,r,vars,u,testgen:=true)
 local Bs,CP,Gt,Ls,M,Md,P,Pd,Qs,Ps,S,d,j,k,m,cs,ct,cont,contrib,flats,facts,U,N,kappa:
 # Preprocessing to get linear functions and powers
 d := nops(vars); 
 if nops(r) <> d then error("Direction is not the right dimension"): fi:

 facts := sqrfree(H);
 Gt := G/facts[1];
 Ls := [seq(k[1],k=facts[2])];
 Ps := [seq(k[2],k=facts[2])];
 Bs := Ls:
 m := nops(Ls):

 for k from 1 to nops(Ls) do
  if degree(Ls[k]) <> 1 then error("Denominator not product of linear factors"); fi:
  ct := subs(seq(v=0,v=vars),Ls[k]):
  if ct=0 then error("Function not analytic at origin"); fi:
  Ls[k] := expand(Ls[k]/ct);
  Gt := Gt/ct^Ps[k]:
  Bs[k] := -[seq(coeff(Ls[k],v),v=vars)]:
 od:

 # Get flats and find contributing points
 flats := combinat[powerset]({seq(k,k=1..m)}) minus {{}}: 
 flats := select(a->nops(a)<=d,flats):

 contrib := {}:
 for S in flats do
    M := Matrix([seq(Bs[k],k=S),[seq(r[k]/vars[k],k=1..d)]]).DiagonalMatrix([seq(vars[k],k=1..d)]); 
    Md := seq((Matrix([seq(c[k],k=1..nops(S)),-1]).M)[1,k],k=1..d); 

    P,Qs := Kronecker([Md,seq(Ls[k],k=S)],1,[op(vars),seq(c[k],k=1..nops(S))],u);

    # Test for no critical points on flat
    if P <> 1 then 
      U,N,kappa := NumericalKronecker(P,Qs,[op(vars),seq(c[k],k=1..nops(S))],u):

      for k from 1 to nops(U) do
        cont := true:
        cs := N[k][-nops(S)..-1]:
        for j in cs do 
          if j<0 then cont := false: fi: if j=0 and testgen then error("Not generic direction"): fi: 
        od:
        if cont then 
          contrib := contrib union {[[P,Qs,U[k]],evalf(N[k][1..-nops(S)-1],10),S]}: 
        fi:
      od:
    fi:
 od:

 return contrib:
end:


##########################################################################################################
# Calculates asymptotic contribution of a contributing singularity of F = G/H
#
# INPUT: 		G - numerator of F
#				H - denominator of F
#				r - direction, containing *positive integers*
#			 vars - ordered list of variables, same length as r
#			sigma - encoding of critical point of F, as given by contribSing above
#			    u - variable (not contained in vars)
#
# OUTPUT:  A - symbolic expression consting of rational functions in u raised to various powers.
#				   R - RootOf expression containing an integer polynomial in u and floating approximation
#				   Asymptotic contribution of F at sigma in direction r is given by setting u=R in A 
#          WILL RETURN 0 IF LEADING CONSTANT IN EXPANSION IS 0 (DOESN'T CHECK HIGHER CONSTANTS)
###########################################################################################################
ASMContrib := proc(G,H,r,vars,sigma,u)
 local v,detHesk,Pd,P,Q,U,T,Tk,Ck,CP,S,d,Gt,facts,Ls,BS,Bs,Ps,ct,j,k,flats,M,Md,MM,MT,MI,m,contrib,cs,cont,c,fl,PivCols,AA,DD,Hes,detHes,C,psi;

 d := nops(vars); 
 facts := sqrfree(H);
 Gt := G/facts[1];
 Ls := [seq(k[1],k=facts[2])];
 Ps := [seq(k[2],k=facts[2])];
 Bs := Ls:
 m := nops(Ls):

 for k from 1 to nops(Ls) do
  if degree(Ls[k]) <> 1 then error("Denominator not product of linear factors"); fi:
  ct := subs(seq(v=0,v=vars),Ls[k]):
  if ct=0 then error("Function not analytic at origin"); fi:
  Ls[k] := expand(Ls[k]/ct);
  Gt := Gt/ct^Ps[k]:
  Bs[k] := -[seq(coeff(Ls[k],v),v=vars)]:
 od:

 P := sigma[1][1];
 Q := sigma[1][2];
 U := sigma[1][3];
 Pd := diff(P,u);

 T := mul(1/vars[k]^r[k],k=1..d); 
 Tk := KroneckerReduce(T,P,Q,vars,u);

 S := sigma[3]; 

 if nops(S)=d then
   M := Matrix([seq(Bs[k],k=S)]); 
   MI := MatrixInverse(M);
   v := convert(Matrix([seq(r[k]/vars[k],k=1..d)]).MI, list);
   C := mul(v[k]^(Ps[S[k]]-1)/factorial(Ps[S[k]]-1),k=1..nops(S)) * Gt / mul(Ls[k]^Ps[k],k={seq(j,j=1..m)} minus S) / abs(Determinant(M)) / mul(vars[k],k=1..d);
   Ck := KroneckerReduce(C,P,Q,vars,u);
   return (Tk/Pd)^n * n^(add(Ps[k],k=S)-d) * (Ck/Pd), RootOf(P,u,U):
 else
   	# Determine parametrizing coordinates on each flat
   	MM := Matrix([seq(Bs[k],k=S)]);
   	MT := Transpose(MM):
   	BS := LinearAlgebra[Basis]({seq(MT[k],k=1..d)}):
   	PivCols := {}:
   	for j in BS do
    for k from 1 to d do
     if Equal(j,MT[k]) then PivCols := PivCols union {k}: break: fi:
   	od:od:
 
    if nops(PivCols) <> nops(S) then error("Error finding pivot columns"); fi;

   	# Compute Hessian matrix H and vector v - change cols of M if needed
   	M := Matrix([seq(Bs[k],k=S),seq(eVect(k,d),k={seq(k,k=1..d)} minus PivCols)]); 
    M := Matrix([seq(M[..,k],k=PivCols),seq(M[..,k],k={seq(k,k=1..d)} minus PivCols)]);

    MI := MatrixInverse(M); 
    v := convert(Matrix([seq(r[k]/vars[k],k=1..nops(S)),seq(0,k=1..d-nops(S))]).MI, list);

   	AA := SubMatrix(MI,1..d,(nops(S)+1..d)):
   	DD := DiagonalMatrix([seq(sqrt(r[k])/vars[k],k=1..d)]):
   	Hes := Transpose(DD.AA) . (DD.AA);
   	detHes := Determinant(Hes);

   	C := mul(v[k]^(Ps[S[k]]-1)/factorial(Ps[S[k]]-1),k=1..nops(S)) * Gt / mul(Ls[k],k={seq(j,j=1..m)} minus S) / mul(vars[k],k=1..d) / abs(Determinant(M));
	  Ck := KroneckerReduce(C,P,Q,vars,u);
	  detHesk := KroneckerReduce(detHes,P,Q,vars,u);

   	return (Tk/diff(P,u))^n * n^(add(Ps[k],k=S) - (nops(S)+d)/2) * sqrt(Pd/detHesk) * (Ck/Pd) / (2*Pi)^((d-nops(S))/2),RootOf(P,u,U):
   fi:

end:


# Possible extension:
# Automatically sort heights of contributing points


