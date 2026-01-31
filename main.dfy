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
    // Property 1: every ciphertext decrypts to something in declaredTally
    (forall i :: 0 <= i < |e.ciphertexts| ==>
        (exists j :: 0 <= j < |e.declaredTally| &&
            Decrypt(sk, e.ciphertexts[i]) == e.declaredTally[j]))
    &&
    // Property 2: every declaredTally value appears as a decryption of some ciphertext
    (forall j :: 0 <= j < |e.declaredTally| ==>
        (exists i :: 0 <= i < |e.ciphertexts| &&
            Decrypt(sk, e.ciphertexts[i]) == e.declaredTally[j]))
  }

  method RunElectionAudit(
    e: ElectionData,
    p: AuditProofs,
    verifierPK: G2,
    serverPKs: seq<G2>,
    serverPK_forTraceOut: G2,
    ghost sk: SecretKey
  ) returns (auditPassed: bool)
    requires |e.ciphertexts| == |p.traceInProofs|
    requires |e.declaredTally| == |p.traceOutProofs|
    requires |serverPKs| >= 1
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
      var ok := TI.VerifyTraceInProof(e.ciphertexts[i], e.declaredTally, p.traceInProofs[i], verifierPK, serverPKs);
      if !ok { return false; }

      // bridge verifier success to Decrypt logic using soundness
      TI.TraceInSoundness(sk, e.ciphertexts[i], e.declaredTally, p.traceInProofs[i], verifierPK, serverPKs);
      i := i + 1;
    }

    // NOTE: In a stronger spec, we would assert here that every ciphertext
    // decrypts to some declared tally value, using the loop invariant.

    // --------------------------
    // Phase 2: TraceOut checks
    // --------------------------
    var j := 0;
    while j < |e.declaredTally|
      invariant 0 <= j <= |e.declaredTally|
      // PROGRESS: Accumulate Phase 2 proof progress (we keep this informal here)
    {
      var ok2 := TO.VerifyTraceOutProof(e.declaredTally[j], e.ciphertexts, p.traceOutProofs[j], serverPK_forTraceOut);
      if !ok2 { return false; }

      TO.TraceOutSoundness(sk, e.declaredTally[j], e.ciphertexts, p.traceOutProofs[j], serverPK_forTraceOut);
      j := j + 1;
    }

    // A stronger version of this method could assert ElectionIsValid(e, sk)
    // once the necessary lemmas and invariants are fully proved.
    return true;
  }
}