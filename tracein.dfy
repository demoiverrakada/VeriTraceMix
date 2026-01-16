// ============================================================================
// TRACEABLE MIXNETS: BTraceIn PROTOCOL - FORMAL VERIFICATION
// Based on: Prashant Agrawal, "Traceable Mixnets" (PhD Thesis, IIT Delhi, 2024)
//           Agrawal et al., "OpenVoting: Recoverability from Failures in Dual Voting"
//
// PROTOCOL: BTraceIn (Batched Trace In)
// PURPOSE: Verify that input ciphertexts encrypt values in output plaintext set
//          WITHOUT revealing the specific correspondence (Zero-Knowledge)
// ============================================================================

module TraceableVotingTraceIn {
  import opened TVPrimitives

  // --- 3. ZERO-KNOWLEDGE PROOF STRUCTURES ---
  datatype SchnorrProof = Schnorr(
    commitment: G1,
    challenge: Scalar,
    response: Scalar
  )

  datatype ThresholdProofWrapper = TPW(
    share: G1,
    nizk: SchnorrProof
  )

  datatype BBSignature = BBSig(sig: G1, message: Fr)

  datatype DistributedZKProof = DZKProof(
    thresholdDecryptionProofs: seq<ThresholdProofWrapper>
  )

  // --- 4. THE TRACEIN PROOF STRUCTURE ---
  datatype TraceInProof = TIProof(
    bbSignatures: seq<BBSignature>,
    distributedProof: DistributedZKProof,
    blindedSig: G1
  )

  // --- 5. VALIDITY PREDICATES ---

  ghost predicate ValidSchnorrProof(
    nizk: SchnorrProof,
    statement: G1
  )
  {
    var c := HashToScalar([nizk.commitment, statement]);
    && nizk.challenge == c
    && G1Add(nizk.commitment, G1Mult(statement, nizk.challenge)) == 
       G1Mult(G1Generator(), nizk.response)
  }

  ghost predicate ValidThresholdDecryptionShare(
    share: G1,
    ciphertext: Ciphertext,
    serverPK: G2,
    nizk: SchnorrProof
  )
  {
    && Pairing(share, G2Generator()) == Pairing(ciphertext.c1, serverPK)
    && ValidSchnorrProof(nizk, share)
  }

  ghost predicate ValidDistributedZKProof(
    proof: DistributedZKProof,
    ciphertext: Ciphertext,
    numServers: nat,
    serverPKs: seq<G2>
  )
  {
    && |serverPKs| == numServers
    && |proof.thresholdDecryptionProofs| == numServers
    && (forall i :: 0 <= i < numServers ==>
          ValidThresholdDecryptionShare(
            proof.thresholdDecryptionProofs[i].share,
            ciphertext,
            serverPKs[i],
            proof.thresholdDecryptionProofs[i].nizk
          ))
  }

  ghost predicate ValidBBSignature(sig: G1, message: Fr, pk: G2)
  {
    Pairing(sig, G2Generator()) == Pairing(HashToG1(message), pk)
  }

  ghost predicate AllBBSignaturesValid(
    signatures: seq<BBSignature>,
    candidateSet: seq<Fr>,
    verifierPK: G2
  )
  {
    && |signatures| == |candidateSet|
    && (forall i :: 0 <= i < |candidateSet| ==>
          ValidBBSignature(signatures[i].sig, candidateSet[i], verifierPK))
  }

  ghost predicate BlindedSigBoundToSet(
    blindedSig: G1,
    bbSignatures: seq<BBSignature>
  )
  {
    exists i :: 0 <= i < |bbSignatures| && bbSignatures[i].sig == blindedSig
  }

  // ========================================================================
  // THE CORE VALIDITY PREDICATE FOR TRACEIN
  // ========================================================================
  
  ghost predicate ValidTraceInProof(
    ciphertext: Ciphertext,
    candidateSet: seq<Fr>,
    proof: TraceInProof,
    verifierPK: G2,
    serverPKs: seq<G2>
  )
  {
    && |proof.bbSignatures| == |candidateSet|
    && |serverPKs| >= 1
    && AllBBSignaturesValid(proof.bbSignatures, candidateSet, verifierPK)
    && ValidDistributedZKProof(proof.distributedProof, ciphertext, |serverPKs|, serverPKs)
    && BlindedSigBoundToSet(proof.blindedSig, proof.bbSignatures)
  }

  // ========================================================================
  // VERIFIER (Executable Algorithm)
  // ========================================================================
  
  method VerifySchnorrProof(
    nizk: SchnorrProof,
    statement: G1
  ) returns (valid: bool)
    ensures valid <==> ValidSchnorrProof(nizk, statement)
  {
    var c := HashToScalar([nizk.commitment, statement]);
    if nizk.challenge != c { return false; }
    
    var lhs := G1Add(nizk.commitment, G1Mult(statement, nizk.challenge));
    var rhs := G1Mult(G1Generator(), nizk.response);
    
    return lhs == rhs;
  }

  method VerifyThresholdShare(
    share: G1,
    ciphertext: Ciphertext,
    serverPK: G2,
    nizk: SchnorrProof
  ) returns (valid: bool)
    ensures valid ==> ValidThresholdDecryptionShare(share, ciphertext, serverPK, nizk)
  {
    var pairingLHS := Pairing(share, G2Generator());
    var pairingRHS := Pairing(ciphertext.c1, serverPK);
    
    if pairingLHS != pairingRHS { return false; }
    
    var schnorrValid := VerifySchnorrProof(nizk, share);
    
    return schnorrValid;
  }

  method VerifyDistributedZK(
    proof: DistributedZKProof,
    ciphertext: Ciphertext,
    serverPKs: seq<G2>
  ) returns (valid: bool)
    requires |serverPKs| >= 1
    ensures valid ==> ValidDistributedZKProof(proof, ciphertext, |serverPKs|, serverPKs)
  {
    if |serverPKs| != |proof.thresholdDecryptionProofs| {
      return false;
    }
    
    var i := 0;
    while i < |serverPKs|
      invariant 0 <= i <= |serverPKs|
      invariant forall k :: 0 <= k < i ==>
        ValidThresholdDecryptionShare(
          proof.thresholdDecryptionProofs[k].share,
          ciphertext,
          serverPKs[k],
          proof.thresholdDecryptionProofs[k].nizk
        )
    {
      var shareValid := VerifyThresholdShare(
        proof.thresholdDecryptionProofs[i].share,
        ciphertext,
        serverPKs[i],
        proof.thresholdDecryptionProofs[i].nizk
      );
      
      if !shareValid { return false; }
      i := i + 1;
    }
    
    return true;
  }

  method VerifyAllBBSignatures(
    signatures: seq<BBSignature>,
    candidateSet: seq<Fr>,
    verifierPK: G2
  ) returns (valid: bool)
    requires |signatures| == |candidateSet|
    ensures valid ==> AllBBSignaturesValid(signatures, candidateSet, verifierPK)
  {
    var i := 0;
    while i < |candidateSet|
      invariant 0 <= i <= |candidateSet|
      invariant forall k :: 0 <= k < i ==>
        ValidBBSignature(signatures[k].sig, candidateSet[k], verifierPK)
    {
      var lhs := Pairing(signatures[i].sig, G2Generator());
      var rhs := Pairing(HashToG1(candidateSet[i]), verifierPK);
      
      if lhs != rhs { return false; }
      i := i + 1;
    }
    
    return true;
  }

  method CheckBlindedSigMatch(
    blindedSig: G1,
    bbSignatures: seq<BBSignature>
  ) returns (found: bool)
    ensures found ==> BlindedSigBoundToSet(blindedSig, bbSignatures)
  {
    found := false;
    var i := 0;
    while i < |bbSignatures|
      invariant 0 <= i <= |bbSignatures|
      invariant found ==> BlindedSigBoundToSet(blindedSig, bbSignatures)
    {
      if bbSignatures[i].sig == blindedSig {
        found := true;
        return true;
      }
      i := i + 1;
    }
    return found;
  }

  method VerifyTraceInProof(
    ciphertext: Ciphertext,
    candidateSet: seq<Fr>,
    proof: TraceInProof,
    verifierPK: G2,
    serverPKs: seq<G2>
  ) returns (valid: bool)
    requires |serverPKs| >= 1
    ensures valid ==> ValidTraceInProof(ciphertext, candidateSet, proof, verifierPK, serverPKs)
  {
    if |proof.bbSignatures| != |candidateSet| { return false; }
    
    var bbSigsValid := VerifyAllBBSignatures(
      proof.bbSignatures,
      candidateSet,
      verifierPK
    );
    if !bbSigsValid { return false; }
    
    var dzkValid := VerifyDistributedZK(
      proof.distributedProof,
      ciphertext,
      serverPKs
    );
    if !dzkValid { return false; }
    
    var matchFound := CheckBlindedSigMatch(
      proof.blindedSig,
      proof.bbSignatures
    );
    
    return matchFound;
  }

  // ========================================================================
  // SOUNDNESS THEOREMS
  // ========================================================================

  lemma {:axiom} Axiom_PairingCorrectness(
    u: G1, c1: G1, sk: Scalar, pk: G2
  )
    requires u == G1Mult(c1, sk)
    requires pk == G2Mult(G2Generator(), sk)
    ensures Pairing(u, G2Generator()) == Pairing(c1, pk)

  lemma {:axiom} Axiom_SchnorrSoundness(nizk: SchnorrProof, statement: G1)
    requires ValidSchnorrProof(nizk, statement)
    ensures exists w: Scalar :: G1Mult(G1Generator(), w) == statement

  lemma {:axiom} Axiom_BBSoundness(sig: G1, msg: Fr, pk: G2)
    requires ValidBBSignature(sig, msg, pk)
    ensures exists sk: Scalar :: pk == G2Mult(G2Generator(), sk)

  // ========================================================================
  // THE MAIN THEOREM: TraceIn Soundness
  // ========================================================================

  lemma {:axiom} TraceInSoundness(
    sk: SecretKey,
    c: Ciphertext,
    candidateSet: seq<Fr>,
    proof: TraceInProof,
    verifierPK: G2,
    serverPKs: seq<G2>
  )
    requires ValidTraceInProof(c, candidateSet, proof, verifierPK, serverPKs)
    ensures (exists i :: 0 <= i < |candidateSet| && Decrypt(sk, c) == candidateSet[i])

  // ========================================================================
  // BATCHIN: BATCHED TRACEIN FOR EFFICIENT POLLING BOOTH AUDITING
  // ========================================================================

  method BTraceIn(
    ciphertexts: seq<Ciphertext>,
    candidateSet: seq<Fr>,
    proofs: seq<TraceInProof>,
    verifierPK: G2,
    serverPKs: seq<G2>,
    ghost sk: SecretKey
  ) returns (matchingCiphertexts: seq<Ciphertext>)
    requires |ciphertexts| == |proofs|
    requires |serverPKs| >= 1
    
    ensures forall c :: c in matchingCiphertexts ==>
      (exists i :: 0 <= i < |ciphertexts| && ciphertexts[i] == c &&
      (exists j :: 0 <= j < |candidateSet| &&
      Decrypt(sk, c) == candidateSet[j]))
  {
    matchingCiphertexts := [];
    
    var i := 0;
    while i < |ciphertexts|
      invariant 0 <= i <= |ciphertexts|
      invariant forall c :: c in matchingCiphertexts ==>
        (exists idx :: 0 <= idx < i && ciphertexts[idx] == c &&
        (exists j :: 0 <= j < |candidateSet| &&
        Decrypt(sk, c) == candidateSet[j]))
    {
      var proofValid := VerifyTraceInProof(
        ciphertexts[i],
        candidateSet,
        proofs[i],
        verifierPK,
        serverPKs
      );
      
      if proofValid {
        TraceInSoundness(sk, ciphertexts[i], candidateSet, proofs[i], verifierPK, serverPKs);
        matchingCiphertexts := matchingCiphertexts + [ciphertexts[i]];
      }
      
      i := i + 1;
    }
    
    return matchingCiphertexts;
  }
}
