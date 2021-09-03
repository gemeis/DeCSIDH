xDBL:=function(P,A)
  v1:=P[1]+P[2];
  v1:=v1^2;
  v2:=P[1]-P[2];
  v2:=v2^2;
  x2:=v1*v2;
  v1:=v1-v2;
  v3:=(A+2)*v1/4;
  v3:=v3+v2;
  v3*:=v1;
  if v3 eq 0 then
    return [0,0];
  end if;
  return [x2/(v3),1];
end function;

xADD:=function(P,Q,PmQ,A)
  if P eq [0,0] then
    return Q;
  elif Q eq [0,0] then
    return P;
  elif PmQ eq [0,0] then
    return xDBL(P,A);
  end if;
  v0:=P[1]+P[2];
  v1:=Q[1]-Q[2];
  v1:=v1*v0;
  v0:=P[1]-P[2];
  v2:=Q[1]+Q[2];
  v2:=v2*v0;
  v3:=v1+v2;
  v3:=v3^2;
  v4:=v1-v2;
  v4:=v4^2;
  v4*:=PmQ[1];
  if v4 eq 0 then
    return [0,0];
  end if;
  return [v3/(v4),1];
end function;

Ladder:=function(m,x,A)
  if m eq 0 then
    return [0,0];
  end if;
  k:=Floor(Log(m)/Log(2));
  mtemp:=m-2^k;
  x0:=x;
  x1:=xDBL(x,A);
  for i in [1..(k)] do
    bin:=2^(k-i);
    if mtemp ge bin then
      x0:=xADD(x0,x1,x,A);
      x1:=xDBL(x1,A);
      mtemp-:=bin;
    else
      x1:=xADD(x0,x1,x,A);
      x0:=xDBL(x0,A);
    end if;
  end for;
  return x0,x1;
end function;



//height is log_2(#points)+1
SubProductTree:=function(points,height)
  Q<x>:=PolynomialRing(Parent(points[1]));
  tree:=[Q!0 : i in [1..2^(height)]];
  //first non binary step :
  for i in [1..#points] do
    tree[2^(height-1)-1+i]:=x-points[i];
  end for;
  for k in [1..(height-1)] do
    for i in [1..2^(height-1-k)] do
      index:=2^(height-1-k)-1+i;
      if tree[2*index+1] eq 0 and tree[2*index] ne 0 then
        tree[index]:=tree[2*index];
      else
        tree[index]:=tree[2*index]*tree[2*index+1];
      end if;
    end for;
  end for;
  return tree;
end function;

SubProductTreePolynomials:=function(polys,height)
  zero:=0*polys[1];
  tree:=[zero : i in [1..2^(height)]];
  //first non binary step :
  for i in [1..#polys] do
    tree[2^(height-1)-1+i]:=polys[i];
  end for;
  for k in [1..(height-1)] do
    for i in [1..2^(height-1-k)] do
      index:=2^(height-1-k)-1+i;
      if tree[2*index+1] eq 0 and tree[2*index] ne 0 then
        tree[index]:=tree[2*index];
      else
        tree[index]:=tree[2*index]*tree[2*index+1];
      end if;
    end for;
  end for;
  return tree;
end function;

MultipointEvaluation:=function(points,tree,P,height)
  zero:=0*tree[1];
  tree_eval:=[zero: i in [1..#tree]];
  tree_eval[1]:= P mod tree[1];
  for k in [1..(height-1)] do
    for i in [1..2^k] do
      index:=2^k-1+i;
      if tree[index] eq 0 then
        tree_eval[index]:=0;
      else
        tree_eval[index]:=tree_eval[Floor(index/2)] mod tree[index];
      end if;
    end for;
  end for;
  eval_multipoint:=[Parent(points[1])!0: i in [1..#points]];
  for i in [1..#points] do

    eval_multipoint[i]:=Evaluate(tree_eval[2^(height-1)-1+i],points[i]);
  end for;
  return eval_multipoint;
end function;


evaluate_isogeny_big_degree:=function(isog,P,l)
	if P eq [0,0] then
		return [0,0];
	end if;
	v:=P[1];
	h1:=isog[1];p1:=isog[2];tree1:=isog[3];poly1:=isog[4];poly2:=isog[5];
	p3:=isog[6];poly4:=isog[7];
  ptemp3:=[UnivariatePolynomial(Evaluate(poly3,2,v)): poly3 in p3];
  poly3:=&*ptemp3;
  denom:=Evaluate(poly1,v)*Evaluate(poly2,v)*Evaluate(poly4,v)*(&*MultipointEvaluation(p1,tree1,poly3,h1));
  if denom eq 0 then
    return [0,0];
  end if;
  ptemp3:=[UnivariatePolynomial(Evaluate(poly3,2,1/v)): poly3 in p3];
  poly3:=&*ptemp3;
  num:=Evaluate(poly1,1/v)*Evaluate(poly2,1/v)*Evaluate(poly4,1/v)*(&*MultipointEvaluation(p1,tree1,poly3,h1));
  // num:=Evaluate(polyB1,v)*Evaluate(polyB2,v)*Evaluate(polyB4,v)*(&*MultipointEvaluation(p1,tree1,polyB3,h1));
  // return [(v*(num/denom)^2),1];
  return [v^l*(num/denom)^2,1];
end function;
kernel_generator_to_isogeny_big_degree:=function(A0,P,l)

  _<o>:=PolynomialRing(Parent(A0));
  E0:=EllipticCurve(o^3+A0*o^2+o);
  m:=Floor(Sqrt(l/2));
  k:=Floor(m/2);
  if m^2+m ge Ceiling(l/2) then
    m:=m-1;
  end if;
  _<x>:=PolynomialRing(Parent(A0));
  _<y,T>:=PolynomialRing(Parent(A0),2);
  p1:=[P[1]];
  // pB1:=[x*P[1]-1];
  Ptemp:=P;
  // Ptempr:=Pr;
  Pdiff:=[0,0];
  // Q:=2*m*P;
  Q:=Ladder(2*m,P,A0);
  // Qtemp:=Q;
  Qtemp:=Q;
  // Qtempr[1] eq Qtemp[1];
  Qdiff:=[0,0];
  // Stemp:=m*P;
  Stemp:=Ladder(m,P,A0);
  // Stemp[1] eq Stempr[1];
  Sdiff:=Stemp;
  // Stemp[1] eq Stempr[1];
  p2:=[Q[1]-x];
  // pB2:=[Q[1]*x-1];
  p3:=[(y-Q[1])^2*T^2 - T*2*(y+Q[1]+y*Q[1]*(2*A0+y+Q[1]))+(y*Q[1]-1)^2];
  // pB3:=[(y-Q[1])^2 - T*2*(y+Q[1]+y*Q[1]*(2*A0+y+Q[1]))+T^2*(y*Q[1]-1)^2];
  p4:=[x-Stemp[1]];
  // pB4:=[(x*Stemp[1]-1)];

  for i in [2..(m-1)] do
    // Ptemp:=Ptemp+P;
    Pttemp:=Ptemp;
    Ptemp:=xADD(Ptemp,P,Pdiff,A0);
    Pdiff:=Pttemp;
    // Ptemp[1] eq Ptempr[1];
    Append(~p1,Ptemp[1]);
    // Append(~pB1,(x*Ptemp[1]-1));
  end for;
  for i in [2..k] do
      // Qtemp+:=Q;
      // Stemp+:=Q;
      Qttemp:=Qtemp;
      Qtemp:=xADD(Qtemp,Q,Qdiff,A0);
      Qdiff:=Qttemp;
      // Qtempr[1] eq Qtemp[1];
      Sttemp:=Stemp;
      Stemp:=xADD(Stemp,Q,Sdiff,A0);
      Sdiff:=Sttemp;

    Append(~p2,(x-Qtemp[1]));
    // Append(~pB2,(x*Qtemp[1]-1));
    Append(~p4,(x-Stemp[1]));
    // Append(~pB4,(x*Stemp[1]-1));
    Append(~p3,(y-Qtemp[1])^2*T^2 - T*2*(y+Qtemp[1]+y*Qtemp[1]*(2*A0+y+Qtemp[1]))+(y*Qtemp[1]-1)^2);
    // Append(~pB3,(y-Qtemp[1])^2- T*2*(y+Qtemp[1]+y*Qtemp[1]*(2*A0+y+Qtemp[1]))+T^2*(y*Qtemp[1]-1)^2);
  end for;
  // R:=(2*k*m+m)*P;
  R:=Ladder(2*k*m+m,P,A0);
  // Rr[1] eq R[1];
  Rdiff:=Ladder(2*k*m+m-1,P,A0);
  Append(~p4,x-R[1]);
  // Append(~pB4,x*R[1]-1);
  // Rtemp:=R;
  Rtemp:=R;
  for i in [(2*k*m+m+1)..Floor(l/2)] do
    // Rtemp:=Rtemp+P;
    Rttemp:=Rtemp;
    Rtemp:=xADD(Rtemp,P,Rdiff,A0);
    Rdiff:=Rttemp;
    // Rtempr[1] eq Rtemp[1];
    Append(~p4,(x-Rtemp[1]));
    // Append(~pB4,(x*Rtemp[1]-1));
  end for;
  h1:=Ceiling(Log(#p1)/Log(2))+1;
  h2:=Ceiling(Log(#p2)/Log(2))+1;
  h3:=Ceiling(Log(#p3)/Log(2))+1;
  h4:=1+Ceiling(Log(#p4)/Log(2))+1;


  tree1:=SubProductTree(p1,h1);
  tree2:=SubProductTreePolynomials(p2,h2);
  tree4:=SubProductTreePolynomials(p4,h4);
  // treeB1:=SubProductTreePolynomials(pB1,h1);
  // treeB2:=SubProductTreePolynomials(pB2,h2);
  // treeB4:=SubProductTreePolynomials(pB4,h4);


	poly1:=tree1[1];poly2:=tree2[1];poly4:=tree4[1];
	isogeny:=<h1,p1,tree1,poly1,poly2,p3,poly4>;
  a:=A0+2;
  d:=A0-2;
  ptemp3:=[UnivariatePolynomial(Evaluate(poly3,2,1)): poly3 in p3];
  poly3:=&*ptemp3;
  prod3:=Evaluate(poly1,1)*Evaluate(poly2,1)*Evaluate(poly4,1)*(&*MultipointEvaluation(p1,tree1,poly3,h1));
  ptemp3:=[UnivariatePolynomial(Evaluate(poly3,2,-1)): poly3 in p3];
  poly3:=&*ptemp3;
  prod4:=Evaluate(poly1,-1)*Evaluate(poly2,-1)*Evaluate(poly4,-1)*(&*MultipointEvaluation(p1,tree1,poly3,h1));
  a1:=a^(l)*prod4^8;
  d1:=d^(l)*prod3^8;
  A:=2*(a1+d1)/(a1-d1);
  return A,isogeny;
end function;

function step_zero_Montgomery_plus(X1, Z1, X2, Z2, X3, Z3, A)
  return (X2^2-Z2^2)^2, 4*X2*Z2*(X2^2+A*X2*Z2+Z2^2), 4*(X2*X3-Z2*Z3)^2*Z1, 4*(X2*Z3-Z2*X3)^2*X1;
end function;


function step_one_Montgomery_plus(X1, Z1, X3, Z3, X2, Z2, A)
  return 4*(X2*X3-Z2*Z3)^2*Z1, 4*(X2*Z3-Z2*X3)^2*X1, (X2^2-Z2^2)^2, 4*X2*Z2*(X2^2+A*X2*Z2+Z2^2);
end function;


function scalar_multiplication_Montgomery_plus(n, X1, Z1, A)
  X2 := 1; Z2 := 0; X3 := X1; Z3 := Z1;
  nbits := Reverse(Intseq(n,2));
  if Z1 eq 0 then return "Error";
  else for i := 1 to #nbits do
    if nbits[i] eq 0 then X2, Z2, X3, Z3 := step_zero_Montgomery_plus(X1, Z1, X2, Z2, X3, Z3, A);
    else X2, Z2, X3, Z3 := step_one_Montgomery_plus(X1, Z1, X2, Z2, X3, Z3, A);
    end if;
  end for;
  return X2, Z2;
  end if;
end function;

find_torsion_point:=function(A,ell)
  F:=Parent(A);
  fac:=(p+1) div ell;
  repeat
    xP := Random(F);
    twist := not IsSquare(xP^3+A*xP^2+xP); if twist then A := -A; xP := -xP; end if;
    zP:=F!1;
    Xl,Zl:=scalar_multiplication_Montgomery_plus(fac,xP,zP,A);
  until Zl ne 0;
  return twist,Xl,Zl;
end function;

function differential_addition_Montgomery_plus(X1, Z1, X2, Z2, X3, Z3, A)
  if X1 eq 0 or Z1 eq 0 or [X2,Z2] eq [0,0] or [X3,Z3] eq [0,0] then return 0, 0;
  else
    return 4*(X2*X3-Z2*Z3)^2*Z1, 4*(X2*Z3-Z2*X3)^2*X1;
  end if;
end function;


function double_point_Montgomery_plus(X2, Z2, A)
  if Z2 eq 0 or X2^3+A*X2^2+X2 eq 0 then return 0, 0;
  else return (X2^2-Z2^2)^2, 4*X2*Z2*(X2^2+A*X2*Z2+Z2^2);
  end if;
end function;


function act_with_small_ell_on_Montgomery_plus(A, ell, xTors, xPush)
  XQ := xTors; ZQ := 1;
  pi := XQ; sigma := XQ - 1/XQ;
  fXPush := (XQ*xPush-1); fZPush := (xPush-XQ);
  if ell eq 3 then return pi^2*(A-6*sigma), xPush*fXPush^2, fZPush^2;
  else
  XQ, ZQ := double_point_Montgomery_plus(XQ, ZQ, A); xQ := XQ/ZQ;
  pi *:= xQ; sigma +:= xQ - 1/xQ;
  fXPush *:= (xQ*xPush-1); fZPush *:= (xPush-xQ);
  XPrev := xTors; ZPrev := 1;
  for i in [3..(ell-1) div 2] do
    XTemp := XQ; ZTemp := ZQ;
    XQ, ZQ := differential_addition_Montgomery_plus(XPrev, ZPrev, xTors, 1, XQ, ZQ, A); xQ := XQ/ZQ;
    pi *:= xQ; sigma +:= xQ - 1/xQ;
    fXPush *:= (xQ*xPush-1); fZPush *:= (xPush-xQ);
    XPrev := XTemp; ZPrev := ZTemp;
  end for;
  end if;
  return pi^2*(A - 6*sigma), xPush*fXPush^2, fZPush^2;
end function;

function act_with_big_ell_on_Montgomery_plus(A, ell, xTors, xPush)
  F:=Parent(xTors);
  Af,isog:=kernel_generator_to_isogeny_big_degree(A,[xTors,F!1],ell);
  fXpush:=evaluate_isogeny_big_degree(isog,[xPush,F!1],ell);
  return Af,fXpush[1],fXpush[2];
end function;

function act_with_ell_on_Montgomery_plus(A,ell,xTors,xPush,degree_bound)
  if ell le degree_bound then
    return act_with_small_ell_on_Montgomery_plus(A,ell,xTors,xPush);
  else
    return act_with_big_ell_on_Montgomery_plus(A,ell,xTors,xPush);
  end if;
end function;

function csidh_action_new(private_key, A,degree_bound)
  F := GF(p);
  // F2:=GF(p^2);
  // A := F2! A;
  // _<o>:=PolynomialRing(F2);
  big_ells:=ells;
  A:=F!A;
  // small_ells:=[];
  // private_key_small:=[];
  // while big_ells[1] le degree_bound do
  //   Append(~small_ells,big_ells[1]);
  //   Remove(~big_ells,1);
  //   Append(~private_key_small,private_key[1]);
  //   private_key:=Remove(private_key,1);
  // end while;
  // alpha:=Roots(o^2+A*o+1)[1][1];
  while private_key ne [0 : i in [1..#private_key]] do
    xP := Random(F);
    twist := not IsSquare(xP^3+A*xP^2+xP); if twist then A := -A; xP := -xP; end if;
    indices_ells_correct_sign := [];
    k := 1;
    for i := 1 to #big_ells do
      if private_key[#big_ells-i+1] gt 0 and not twist then Append(~indices_ells_correct_sign,#big_ells-i+1); k *:= big_ells[#big_ells-i+1];
    elif private_key[#big_ells-i+1] lt 0 and twist then Append(~indices_ells_correct_sign,#big_ells-i+1); k *:= big_ells[#big_ells-i+1];
      end if;
    end for;
    XQ, ZQ := scalar_multiplication_Montgomery_plus((p+1) div k, xP, 1, A);
    for i in indices_ells_correct_sign do
      if ZQ ne 0 then
        xQ := XQ/ZQ;
        ell := big_ells[i];
        // k := k div ell;
        XR, ZR := scalar_multiplication_Montgomery_plus(k div ell, xQ, 1, A);
        if ZR ne 0 then
          // private_key;
          A, XQ, ZQ := act_with_ell_on_Montgomery_plus(A, ell, XR/ZR, xQ,degree_bound);
          if twist then private_key[i] +:= 1; else private_key[i] -:= 1; end if;
        end if;
      end if;
    end for;
    if twist then A := -A; end if;
  end while;
  // while private_key_small ne [0 : i in [1..#private_key_small]] do
  //   xP := F2!Random(F);
  //   twist := not IsSquare(F!(xP^3+A*xP^2+xP)); if twist then A := -A; xP := -xP; end if;
  //   indices_ells_correct_sign := [];
  //   k := 1;
  //   for i := 1 to #small_ells do
  //     if private_key_small[i] gt 0 and not twist then Append(~indices_ells_correct_sign,i); k *:= small_ells[i];
  //   elif private_key_small[i] lt 0 and twist then Append(~indices_ells_correct_sign,i); k *:= small_ells[i];
  //     end if;
  //   end for;
  //   XQ, ZQ := scalar_multiplication_Montgomery_plus((p+1) div k, xP, 1, A);
  //   for i in indices_ells_correct_sign do
  //     if ZQ ne 0 then
  //       xQ := XQ/ZQ;
  //       ell := small_ells[i];
  //       XR, ZR := scalar_multiplication_Montgomery_plus(k div ell, xQ, 1, A);
  //       if ZR ne 0 then
  //         // private_key;
  //         A, XQ, ZQ := act_with_small_ell_on_Montgomery_plus(A, ell, XR/ZR, xQ);
  //         if twist then private_key_small[i] +:= 1; else private_key_small[i] -:= 1; end if;
  //       end if;
  //     end if;
  //   end for;
  //   if twist then A := -A; end if;
  // end while;
  return A;
end function;

function csidh_action_old(private_key,A)
  p := 2^2*&*ells - 1;
  F := GF(p);
  A := F ! A;
  while private_key ne [0 : i in [1..n]] do
    xP := Random(F);
    twist := not IsSquare(xP^3+A*xP^2+xP); if twist then A := -A; xP := -xP; end if;
    indices_ells_correct_sign := [];
    k := 1;
    for i := 1 to #ells do
      if private_key[#ells-i+1] gt 0 and not twist then Append(~indices_ells_correct_sign,#ells-i+1); k *:= ells[#ells-i+1];
    elif private_key[#ells-i+1] lt 0 and twist then Append(~indices_ells_correct_sign,#ells-i+1); k *:= ells[#ells-i+1];
      end if;
    end for;
    XQ, ZQ := scalar_multiplication_Montgomery_plus((p+1) div k, xP, 1, A);
    for i in indices_ells_correct_sign do
      if ZQ ne 0 then
        xQ := XQ/ZQ;
        ell := ells[i];
        // k:=k div ell;
        XR, ZR := scalar_multiplication_Montgomery_plus(k div ell, xQ, 1, A);
        // private_key;
        if ZR ne 0 then
          A, XQ, ZQ := act_with_small_ell_on_Montgomery_plus(A, ell, XR/ZR, xQ);
          if twist then private_key[i] +:= 1; else private_key[i] -:= 1; end if;
        end if;
      end if;
    end for;
    if twist then A := -A; end if;
  end while;
  return A;
end function;


function csidh_private_keygen()
  return [Random([-B..B]) : i in [1..n]];
end function;


procedure csidh_key_exchange()
  print "Note: this takes about 5 minutes!";
  degree_bound:=150;
  alice_private := csidh_private_keygen();
  bob_private := csidh_private_keygen();
/*  t := Cputime();
  alice_public := csidh_action_old(alice_private,0);
  // printf "Alice's public key is %o.\n", alice_public;
  bob_public := csidh_action_old(bob_private,0);
  // printf "Bob's public key is %o.\n", bob_public;
  alice_bob := csidh_action_old(alice_private, bob_public);
  bob_alice := csidh_action_old(bob_private, alice_public);
  key1:=alice_bob;
  if alice_bob ne bob_alice then
    print "Error! The computations of the joint key do not match in the old version.";
  else
    printf "old time : %o\n", Cputime(t);
    // printf "The joint key is %o.\n", alice_bob;
  end if;
*/
  t := Cputime();
  alice_public := csidh_action_new(alice_private,0,degree_bound);
  // printf "Alice's public key is %o.\n", alice_public;
  bob_public := csidh_action_new(bob_private,0,degree_bound);
  // printf "Bob's public key is %o.\n", bob_public;
  alice_bob := csidh_action_new(alice_private, bob_public,degree_bound);
  bob_alice := csidh_action_new(bob_private, alice_public,degree_bound);
  if alice_bob ne bob_alice then
    print "Error! The computations of the joint key do not match in the new version.";
  else
    printf "new time : %o\n", Cputime(t);
    // printf "The joint key is %o.\n", alice_bob;
  end if;
  alice_bob eq bob_alice;
end procedure;



sort_insert:=function(list,val)
  if list eq [] then
    return [val];
  end if;
  low:=[];
  big:=list;
  A:=big[1];
  while A le val and big ne [] do
    Append(~low,A);
    Remove(~big,1);
    if big eq [] then
      break;
    else
      A:=big[1];
    end if;
  end while;
  Append(~low,val);
  l:=low cat big;
  return l;
end function;

function benchmark_old(lot,repet)
  alice_private := [B: i in [1..n]];
  values:=[];
  for i in [1..repet] do
    t:=Cputime();
    for j in [1..lot] do
      x:=csidh_action_old(alice_private,0);
    end for;
    t:=Cputime(t)/lot;
    values:=sort_insert(values,t);
  end for;
  return values[#values div 2+1];
end function;

function benchmark_new(lot,repet,degree_bound,max)
 	if max then
    alice_private := [B: i in [1..n]];
  else
    alice_private:=csidh_private_keygen();
  end if;
  values:=[];
  for i in [1..repet] do
    t:=Cputime();
    for j in [1..lot] do
      x:=csidh_action_new(alice_private,0,degree_bound);
    end for;
    t:=Cputime(t)/lot;
    values:=sort_insert(values,t);
    if not max then
      alice_private:=csidh_private_keygen();
    end if;
  end for;
  return values[#values div 2+1];
end function;

// function benchmark_new(lot,repet,degree_bound)
//   alice_private := [B: i in [1..n]];
//   values:=[];
//   for i in [1..repet] do
//     t:=Cputime();
//     for j in [1..lot] do
//       x:=csidh_action_new(alice_private,0,degree_bound);
//     end for;
//     t:=Cputime(t)/lot;
//     values:=sort_insert(values,t);
//   end for;
//   return values[#values div 2+1];
// end function;

procedure benchmark()
  lot:=1;
  repet:=1;
  "median upon ",repet," means on batches of size ",lot;
  degree_bounds:=[113,1000];
  //degree_bounds:=[150];
  times:=[];
  // old_time:=be:nchmark_old(lot,repet,max);
  // old_time;
  max:=true;
  for degree_bound in degree_bounds do
  Append(~times,benchmark_new(lot,repet,degree_bound,max));
  end for;
  "Results for maximal keys :";
  "degree_bound,time(s),ratio";
  old_time:=times[#times];
  for i in [1..#times] do printf "%o,%o,%o\n",degree_bounds[i],times[i],times[i]/old_time; end for;

  times:=[];
  max:=false;
  for degree_bound in degree_bounds do
  Append(~times,benchmark_new(lot,repet,degree_bound,max));
  end for;
  "Results for Random keys :";
  "degree_bound,time(s),ratio";
  old_time:=times[#times];
  for i in [1..#times] do printf "%o,%o,%o\n",degree_bounds[i],times[i],times[i]/old_time; end for;
  // "percents of improvements":
  // for i in |1..#times] do printf "%o",; end for;
  // printf "%o,%o\n",times[#times];
  // for i in [1..#times-1] do printf "%o,",degree_bounds[i]; end for;
  // printf "%o\n",degree_bounds[#times];
end procedure;

procedure benchmark_action()
  // "#Speed test for isogeny computation over Fp with Log(p)=";
  // "#performed on zardoz, 3.40 Ghz, intel i7-6700 with 64Go RAM";
  // "old CSIDH action (s):";
  lot:=2;
  repet:=3;
  degree_bound:=100;
  // degree_bounds:=[150];
  // degree_bounds:=[50,100,150,200];
  // times:=[];
  // benchmark_old(lot,repet);
  // for degree_bound in degree_bounds do
  //   Append()
  //   Append(~times,benchmark_new(lot,repet,degree_bound));
  // end for;
  for i in [1..repet] do
    old:=[];
    new:=[];
    for j in [1..lot] do
      private:=csidh_private_keygen();
      t1:=ClockCycles();
      _:=csidh_action_old(private,0);
      Append(~old,ClockCycles()-t1);
      t1:=ClockCycles();
      _:=csidh_action_new(private,0,degree_bound);
      Append(~new,ClockCycles()-t1);
    end for;
    printf "action cycles ";
    for n in new do
      printf "%o ",n;
    end for;
    printf "baseline ";
    for o in old do
      printf "%o ",o;
    end for;
    printf "\n";
  end for;
  // "#the degree bound is the limit after which isogeny of this degree are evaluated using the new method in CSIDH";
  // "degree_bound,time (s)";
  // for i in [1..#times] do printf "%o,%o\n",degree_bounds[i],times[i]; end for;
  // printf "%o,%o\n",times[#times];
  // for i in [1..#times-1] do printf "%o,",degree_bounds[i]; end for;
  // printf "%o\n",degree_bounds[#times];
end procedure;

procedure benchmark_isogeny()

  repet:=15;
  F:=GF(p);
  A:= csidh_action_old(csidh_private_keygen(),0);

  for ell in ells do
    new:=[];
    old:=[];
    if ell ne 3 then
      for i in [1..repet] do
        twist,Xl,Zl:=find_torsion_point(A,ell);
        if twist then A := -A; end if;
        xQ:=Random(F);
        t1:=ClockCycles();
        _:=act_with_small_ell_on_Montgomery_plus(A,ell,Xl/Zl,xQ);
        Append(~old,ClockCycles()-t1);
        t2:=ClockCycles();
        _:=act_with_big_ell_on_Montgomery_plus(A,ell,Xl/Zl,xQ);
        Append(~new,ClockCycles()-t2);
      end for;
      printf "l %o cycles ",ell;
      for n in new do
        printf "%o ",n;
      end for;
      printf "baseline ";
      for o in old do
        printf "%o ",o;
      end for;
      printf "\n";
    end if;

  end for;
end procedure;

if false then
  print "csidh_key_exchange():";
  csidh_key_exchange();
  print "benchmark()";
  benchmark();
  print "benchmark_action()";
  benchmark_action();
  print "benchmark_isogeny()";
  benchmark_isogeny();
end if;
