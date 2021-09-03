ms := 0; //increase for higher verifiablity - doesn't change delegator gain
degree_bound := 150;

function Tim()
  //return Cputime();
  return ClockCycles();
end function;


function csidh_private_keygen(n,B) //redefine keygen with parameters
  return [Random([-B..B]) : i in [1..n]];
end function;



// ======================== //
// === Split and ShrVec === //
// ======================== //

function Split(s,k)
    Cs := RandomSubset({1..#s},k);
    ss := []; sp := [];
    for i:=1 to #s do
      if i in Cs then Append(~ss,s[i]); Append(~sp,0);
      else            Append(~ss,0); Append(~sp,s[i]);
      end if;
    end for;
    return ss,sp;
end function;

function ShrVec(s,delta,B)
  R0:=[]; R1:=[]; RS:=[];
  for i:=1 to #s do
    if delta gt 0 then //standard case
      repeat
        r0 := Random(-(delta+1)*B,(delta+1)*B);
        r1 := s[i]-r0;
      until ( (AbsoluteValue(r0) le delta*B) or (AbsoluteValue(r1) le delta*B) );

      b := Random(1);
      if (AbsoluteValue(r0) gt delta*B) then
        if b eq 0 then r1:=Random(delta*B); end if;
        r0 := -r1;
        rs := s[i];
      elif (AbsoluteValue(r1) gt delta*B) then
        if b eq 0 then r0:=Random(delta*B); end if;
        r1 := -r0;
        rs := s[i];
      else rs := 0;
      end if;
    else // delta = 0 corresponds to delta = infty or to Cl(O) known
      repeat // these r0,r1 are not uniform! this case is just representative!
        r0 := Random(-B,B);
        r1 := s[i]-r0;
      until ( (AbsoluteValue(r0) le B) and (AbsoluteValue(r1) le B) );
      rs := 0;
    end if;

    Append(~R0,r0); Append(~R1,r1); Append(~RS,rs);
  end for;
  return R0,R1,RS;
end function;

function Split_and_Shroud(s,delta,B,k)
    if k eq 0 then
      SS := [0 : i in [1..#s]];
      SP := s;
    else SS,SP := Split(s,k);
    end if;
    R0,R1,RS := ShrVec(SP,delta,B);
    return R0,R1,RS,SS;
end function;




// ============================== //
// === Delegation subroutines === //
// ============================== //

function ISO_2HBC(private_key,A,delta,B,k : server := false)
    E := GF(p)!A;

    // Shrouding step
    t:=Tim();
      r0,r1,rs,ss := Split_and_Shroud(private_key,delta,B,k);
    TD:=Tim()-t;

    // First Delegation
    t:=Tim();
      if server then E := csidh_action_new(r0,E,degree_bound); end if;
    Ts1:=Tim()-t;

    // Action of rstar
    t:=Tim();
      E := csidh_action_new(rs,E,degree_bound);
    TD+:=Tim()-t;

    // Second Delegation
    t:=Tim();
      if server then E := csidh_action_new(r1,E,degree_bound); end if;
    Ts2:=Tim()-t;

    // Action of sstar
    if k ne 0 then // if k eq 0 --> CIso, else HIso
    t:=Tim();
      E := csidh_action_new(ss,E,degree_bound);
    TD+:=Tim()-t;
    end if;

    return TD,Ts1,Ts2,E;  // cost of delegator, server1, server2 ; codomain
end function;


function ISO_OMTUP(private_key,A,delta,B,k : server := false)
    E := GF(p)!A;
    n := #private_key;
    mr := 3;

    // Shrouding step
    t:=Tim();
      a1,a2,as,ss := Split_and_Shroud(private_key,delta,B,k);
      sp          := [a1[i]+a2[i]+as[i] : i in [1..n]];
      b1,b2,bs,_  := ShrVec(sp,delta,B); // make sure to have the same sp and ss
      e           := [csidh_private_keygen(n,delta*B) : i in [1..mr]]; //R
      c1:=[[]]; c2:=[[]]; d1:=[[]]; d2:=[[]];
      for m:=1 to ms do
        Append(~c1,[]); Append(~c2,[]); Append(~d1,[]); Append(~d2,[]);
        for i:=1 to n do
          repeat
            _c1 := Random(-delta*B,delta*B);
            _c2 := Random(-delta*B,delta*B);
            _d1 := Random(-delta*B,delta*B);
            _d2 := _c1+_c2-_d1;
          until AbsoluteValue(_d2) le delta*B;
          Append(~c1[m],_c1); Append(~c2[m],_c2); Append(~d1[m],_d1); Append(~d2[m],_d2); //S
        end for;
      end for;
    TD:=Tim()-t;
    //printf "Shrouding step time: %o", TD;

    // First Delegation Step
    t:=Tim();
      if server then
        Ea1 := csidh_action_new(a1,A,degree_bound);
        Ec1 := [csidh_action_new(c1[i],A,degree_bound) : i in [1..ms]];
        Ee1 := [csidh_action_new(e[i],A,degree_bound)  : i in [1..mr]];
      end if;
    Ts1:=Tim()-t;
    t:=Tim();
      if server then
        Eb1 := csidh_action_new(b1,A,degree_bound);
        Ed1 := [csidh_action_new(d1[i],A,degree_bound) : i in [1..ms]];
        Ee2 := [csidh_action_new(e[i],A,degree_bound)  : i in [1..mr]];
      end if;
    Ts2:=Tim()-t;
    if not server then Ea1:=E; Eb1:=E; end if;
    //printf "First delegation step: %o", Ts1+Ts2+TD;


    // Verification and action of astar,bstar
    t:=Tim();
      if server and (Ee1 ne Ee2) then print "Curves do not match after round 1"; return 1; end if;
      Ea1 := csidh_action_new(as,Ea1,degree_bound);
      Eb1 := csidh_action_new(bs,Eb1,degree_bound);
    TD+:=Tim()-t;
    //printf "Star action step: %o", Ts1+Ts2+TD;

    // Second Delegation Step
    t:=Tim();
      if server then
        Es1 := csidh_action_new(a2,Ea1,degree_bound);
        Ed2 := [csidh_action_new(d2[i],Ed1[i],degree_bound) : i in [1..ms]];
      end if;
    Ts1+:=Tim()-t;
    t:=Tim();
      if server then
        Es2 := csidh_action_new(b2,Eb1,degree_bound);
        Ec2 := [csidh_action_new(c2[i],Ec1[i],degree_bound) : i in [1..ms]];
      end if;
    Ts2+:=Tim()-t;
    //printf "Second delegation step: %o", Ts1+Ts2+TD;


    // Verification
    t:=Tim();
      if server then
        if Ed2 ne Ec2 then print "Curves do not match after round 2"; return 1; end if;
        if Es1 ne Es2 then print "Curves do not match after round 2"; return 1; end if;
      end if;
    TD+:=Tim()-t;
    //printf "Verification step: %o", Ts1+Ts2+TD;
    if not server then Es1 := Ea1; end if;

    // Action of sstar
    if k ne 0 then
    t:=Tim();
      Es1 := csidh_action_new(ss,Es1,degree_bound);
    TD+:=Tim()-t;
    end if;
    //printf "Sstar action step: %o", Ts1+Ts2+TD;

    return TD,Ts1,Ts2,Es1;
end function;




// =============================== //
// === Cryptographic Protocols === //
// =============================== //

// a) Local Versions

function local_csidh(n,B)
  a := csidh_private_keygen(n,B);
  b := csidh_private_keygen(n,B);

  t := Tim();
    EA := csidh_action_new(a,0,degree_bound);
  T := Tim()-t;

  EB  := csidh_action_new(b,0,degree_bound);
  EAB := csidh_action_new(b,EA,degree_bound);

  t := Tim();
    EBA := csidh_action_new(a,EB,degree_bound);
  T+:= Tim()-t;

  if EBA ne EAB then print "Joint key does not match."; end if;
  return T;
end function;

function local_ID(n,B) // binary ID protocol (underlying Seasign)
  a := csidh_private_keygen(n,B);
  t := Tim();
    EA := csidh_action_new(a,0,degree_bound);
  T := Tim()-t;
  return T;
end function;






// b) Delegated Versions

function Delegated_CSIDH(n,B,delta,k,assumption : server := false)
  a := csidh_private_keygen(n,B); //delegator (alice)
  b := csidh_private_keygen(n,B); //bob

  EB := csidh_action_new(b,0,degree_bound); // Bob

  if assumption eq "2HBC" then
    T1,Ts1_1,Ts2_1,EA  := ISO_2HBC(a,0,delta,B,0 : server:=server);
    T2,Ts1_2,Ts2_2,EBA := ISO_2HBC(a,EB,delta,B,k: server:=server);
  elif assumption eq "OMTUP" then
    T1,Ts1_1,Ts2_1,EA  := ISO_OMTUP(a,0,delta,B,0 : server:=server);
    T2,Ts1_2,Ts2_2,EBA := ISO_OMTUP(a,EB,delta,B,k: server:=server);
  else print "WRONG ASSUMPTION INDICATOR";
  end if;

  if server then
    EAB   := csidh_action_new(b,EA,degree_bound); // Bob
    if EBA ne EAB then print "Joint key does not match."; end if;
  end if;
  return T1+T2,Ts1_1+Ts1_2,Ts2_1+Ts2_2;
end function;


function Delegated_ID(n,B,delta,assumption : server:=false)
  a := csidh_private_keygen(n,B);
  t := Tim();
    EA := csidh_action_new(a,0,degree_bound);
  T := Tim()-t;
  if assumption eq "2HBC" then
    T1,Ts1,Ts2,EA  := ISO_2HBC(a,0,delta,B,0 : server:=server);
  elif assumption eq "OMTUP" then
    T1,Ts1,Ts2,EA  := ISO_OMTUP(a,0,delta,B,0 : server:=server);
  else print "WRONG ASSUMPTION INDICATOR";
  end if;
  return T1,Ts1,Ts2,EA;
end function;




// c) benchmarks

procedure benchmark_CSIDH(delta,N : server:=false) // N = number of repetitions
  server := false; //do not perform the server actions
                   //(this makes the benchmarks much quicker but returns incorrect results
                   // for correct results, set server := true; )

  // LOCAL
  T_local := 0;
  for i:=1 to N do T_local +:= local_csidh(n,B); end for;
  T_local := T_local/N;
  printf "  local cost     : %o (%.5o)\n", T_local,  T_local /T_local/1.0/1.0;

  // HBC
  T_2hbc:=0; Ts1_2hbc:=0; Ts2_2hbc:=0;
  for i:=1 to N do
    t_2hbc, ts1_2hbc, ts2_2hbc   := Delegated_CSIDH(n,B,delta,k,"2HBC" : server:=server);
    T_2hbc+:=t_2hbc; Ts1_2hbc+:=ts1_2hbc; Ts2_2hbc+:=ts2_2hbc;
  end for;
  T_2hbc:=T_2hbc/N/1.0; Ts1_2hbc:=Ts1_2hbc/N/1.0; Ts2_2hbc:=Ts2_2hbc/N/1.0;
  printf "  2HBC           : %.1o (%.5o)\n", T_2hbc,   T_2hbc  /T_local/1.0;
  if server then
    printf "  2HBC (server)  : %.1o (%.5o)\n", Ts1_2hbc, Ts1_2hbc/T_local/1.0;
  end if;
  //printf "  2HBC (server)  : %.1o (%.5o)\n", Ts2_2hbc, Ts2_2hbc/T_local/1.0;

  // OMTUP
  T_omtup:=0; Ts1_omtup:=0; Ts2_omtup:=0;
  for i:=1 to N do
    t_omtup, ts1_omtup, ts2_omtup := Delegated_CSIDH(n,B,delta,k,"OMTUP" : server:=server);
    T_omtup+:=t_omtup; Ts1_omtup+:=ts1_omtup; Ts2_omtup+:=ts2_omtup;
  end for;
  T_omtup:=T_omtup/N/1.0; Ts1_omtup:=Ts1_omtup/N/1.0; Ts2_omtup:=Ts2_omtup/N/1.0;
  printf "  OMTUP          : %.1o (%.5o)\n", T_omtup,  T_omtup /T_local/1.0;
  if server then
    printf "  OMTUP (server) : %.1o (%.5o)\n", Ts1_omtup,Ts1_omtup/T_local/1.0;
  end if;
  //printf "  OMTUP (server) : %.1o (%.5o)\n", Ts2_omtup,Ts2_omtup/T_local/1.0;
end procedure;




procedure benchmark_ID(delta,N : server:=false) // N = number of repetitions
  //server := false; //do not perform the server actions
                   //(this makes the benchmarks much quicker but returns incorrect results
                   // for correct results, set server := true; )

  // LOCAL
  T_local := 0;
  for i:=1 to N do T_local +:= local_ID(n,B); end for;
  T_local := T_local/N;
  printf "  local cost     : %o (%.5o)\n", T_local,  T_local /T_local/1.0/1.0;

  // HBC
  T_2hbc:=0; Ts1_2hbc:=0; Ts2_2hbc:=0;
  for i:=1 to N do
    t_2hbc, ts1_2hbc, ts2_2hbc   := Delegated_ID(n,B,delta,"2HBC" : server:=server);
    T_2hbc+:=t_2hbc; Ts1_2hbc+:=ts1_2hbc; Ts2_2hbc+:=ts2_2hbc;
  end for;
  T_2hbc:=T_2hbc/N/1.0; Ts1_2hbc:=Ts1_2hbc/N/1.0; Ts2_2hbc:=Ts2_2hbc/N/1.0;
  printf "  2HBC           : %.1o (%.5o)\n", T_2hbc,   T_2hbc  /T_local/1.0;
  if server then
    printf "  2HBC (server)  : %.1o (%.5o)\n", Ts1_2hbc, Ts1_2hbc/T_local/1.0;
  end if;
  //printf "  2HBC (server)  : %.1o (%.5o)\n", Ts2_2hbc, Ts2_2hbc/T_local/1.0;

  // OMTUP
  T_omtup:=0; Ts1_omtup:=0; Ts2_omtup:=0;
  for i:=1 to N do
    t_omtup, ts1_omtup, ts2_omtup := Delegated_ID(n,B,delta,"OMTUP" : server:=server);
    T_omtup+:=t_omtup; Ts1_omtup+:=ts1_omtup; Ts2_omtup+:=ts2_omtup;
  end for;
  T_omtup:=T_omtup/N/1.0; Ts1_omtup:=Ts1_omtup/N/1.0; Ts2_omtup:=Ts2_omtup/N/1.0;
  printf "  OMTUP          : %.1o (%.5o)\n", T_omtup,  T_omtup /T_local/1.0;
  if server then
    printf "  OMTUP (server) : %.1o (%.5o)\n", Ts1_omtup,Ts1_omtup/T_local/1.0;
  end if;
  //printf "  OMTUP (server) : %.1o (%.5o)\n", Ts2_omtup,Ts2_omtup/T_local/1.0;
end procedure;







procedure benchmark_ShrVec(delta,B,n,N)
  T:=0;
  for i:=1 to N do
    s := csidh_private_keygen(n,B);
    t := Tim();
      _,_,_,_ := ShrVec(s,delta,B,0);
    T +:= Tim()-t;
  end for;
  print T/N/1.0;
end procedure;












// Verification procedures

function Exp(s)
  E := 0; n:=#s/1.0;
  for i:=1 to #s do E+:=AbsoluteValue(s[i])/n; end for;
  return E;
end function;

function Verify_Exp(delta,B,n,N)
  Er0 := 0.0; Er1 := 0.0; Ers := 0.0;
  for i:=1 to N do
    s := csidh_private_keygen(n,B);
    r0,r1,rs,_ := ShrVec(s,delta,B,0);
    Er0 +:= Exp(r0)/N; Er1 +:= Exp(r1)/N; Ers +:= Exp(rs)/N;
  end for;
  return Er0,Er1,Ers;
end function;

