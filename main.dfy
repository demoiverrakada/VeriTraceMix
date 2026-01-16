// main.dfy
module TraceableVotingAudit {

  import opened TVPrimitives
  import TI = TraceableVotingTraceIn
  import TO = TraceableVotingTraceOut

  datatype ElectionData = Election(
    ciphertexts: seq<Ciphertext>,
    declaredTally: seq<Fr>
  )

  datatype AuditProofs = Audit(
    traceInProofs: seq<TI.TraceInProof>,
    traceOutProofs: seq<TO.TraceOutProof>
  )

  ghost predicate ElectionIsValid(e: ElectionData, sk: SecretKey)
  {
    // Property 1 (TraceIn-style): every ciphertext decrypts to something in declaredTally
    (forall i :: 0 <= i < |e.ciphertexts| ==>
        (exists j :: 0 <= j < |e.declaredTally| &&
            Decrypt(sk, e.ciphertexts[i]) == e.declaredTally[j]))
    &&
    // Property 2 (TraceOut-style): every declaredTally value appears as a decryption of some ciphertext
    (forall j :: 0 <= j < |e.declaredTally| ==>
        (exists i :: 0 <= i < |e.ciphertexts| &&
            Decrypt(sk, e.ciphertexts[i]) == e.declaredTally[j]))
  }

  method RunElectionAudit(
    e: ElectionData,
    p: AuditProofs,
    verifierPK: G2,         // used by TraceIn
    serverPKs: seq<G2>,      // used by TraceIn
    serverPK_forTraceOut: G2,// used by TraceOut (your TraceOut takes a single pk)
    ghost sk: SecretKey
  ) returns (auditPassed: bool)
    requires |e.ciphertexts| == |p.traceInProofs|
    requires |e.declaredTally| == |p.traceOutProofs|
    requires |serverPKs| >= 1
    ensures auditPassed ==> ElectionIsValid(e, sk)
  {
    // --------------------------
    // Phase 1: TraceIn checks
    // --------------------------
    var i := 0;
    while i < |e.ciphertexts|
      invariant 0 <= i <= |e.ciphertexts|
      invariant forall k :: 0 <= k < i ==>
        (exists j :: 0 <= j < |e.declaredTally| &&
           Decrypt(sk, e.ciphertexts[k]) == e.declaredTally[j])
    {
      var ok := TI.VerifyTraceInProof(
        e.ciphertexts[i],
        e.declaredTally,
        p.traceInProofs[i],
        verifierPK,
        serverPKs
      );

      if !ok {
        return false;
      }

      // bridge verifier->semantics using the soundness axiom
      TI.TraceInSoundness(sk, e.ciphertexts[i], e.declaredTally, p.traceInProofs[i], verifierPK, serverPKs);

      i := i + 1;
    }

    // At loop exit, i == |e.ciphertexts|
    assert i == |e.ciphertexts|;

    // Lift loop invariant to full Property 1
    assert forall ii :: 0 <= ii < |e.ciphertexts| ==>
      (exists jj :: 0 <= jj < |e.declaredTally| &&
        Decrypt(sk, e.ciphertexts[ii]) == e.declaredTally[jj]);


    // --------------------------
    // Phase 2: TraceOut checks
    // --------------------------
    var j := 0;
    while j < |e.declaredTally|
      invariant 0 <= j <= |e.declaredTally|
      invariant forall t :: 0 <= t < j ==>
        (exists idx :: 0 <= idx < |e.ciphertexts| &&
           Decrypt(sk, e.ciphertexts[idx]) == e.declaredTally[t])
    {
      var ok2 := TO.VerifyTraceOutProof(
        e.declaredTally[j],
        e.ciphertexts,
        p.traceOutProofs[j],
        serverPK_forTraceOut
      );

      if !ok2 {
        return false;
      }

      // bridge verifier->semantics using the soundness axiom
      TO.TraceOutSoundness(sk, e.declaredTally[j], e.ciphertexts, p.traceOutProofs[j], serverPK_forTraceOut);

      j := j + 1;
    }

    // At loop exit, j == |e.declaredTally|
    assert j == |e.declaredTally|;

    // Lift loop invariant to full Property 2
    assert forall jj :: 0 <= jj < |e.declaredTally| ==>
      (exists ii :: 0 <= ii < |e.ciphertexts| &&
        Decrypt(sk, e.ciphertexts[ii]) == e.declaredTally[jj]);

    assert ElectionIsValid(e, sk);
    return true;
  }
}
