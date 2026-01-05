module TraceableVotingTraceIn {
  
  type G1(==, !new)
  type G2(==, !new)
  type GT(==, !new)
  type Scalar(==, !new)
  type Fr(==, !new)
  
  type PublicKey = G2
  type SecretKey = Scalar
  
  datatype Ciphertext = CT(c1: G1, c2: G1)
  
  function G1Generator(): G1
  function G2Generator(): G2
  function G1Mult(g: G1, s: Scalar): G1
  function G1Add(a: G1, b: G1): G1
  function G2Mult(g: G2, s: Scalar): G2
  function GTExp(gt: GT, s: Scalar): GT
  function Pairing(g1: G1, g2: G2): GT
  function ScalarMult(a: Scalar, b: Scalar): Scalar
  function HashToScalar(data: seq<G1>): Scalar
  function HashToG1(m: Fr): G1
  
  ghost function Decrypt(sk: SecretKey, c: Ciphertext): Fr
  
  datatype SchnorrProof = Schnorr(
    commitment: G1,
    challenge: Scalar,
    response: Scalar
  )
  
  datatype ThresholdProofWrapper = TPW(
    share: G1,
    nizk: SchnorrProof
  )
  
  datatype BBSignature = BBSig(
    sig: G1,
    message: Fr
  )
  
  datatype DistributedZKProof = DZKProof(
    thresholdDecryptionProofs: seq<ThresholdProofWrapper>
  )
  
  datatype TraceInProof = TIProof(
    bbSignatures: seq<BBSignature>,
    distributedProof: DistributedZKProof,
    blindedSig: G1
  )
  
  ghost function FindDiscreteLog(g: G1, h: G1): Scalar
  predicate ComputationallyInfeasible(x: Scalar)
  
  lemma {:axiom} Axiom_DiscreteLogHardness()
    ensures forall g: G1, x: Scalar :: 
      ComputationallyInfeasible(FindDiscreteLog(g, G1Mult(g, x)))
  
  lemma {:axiom} Axiom_PairingBilinearity()
    ensures forall a: Scalar, b: Scalar, g: G1, h: G2 ::
      Pairing(G1Mult(g, a), G2Mult(h, b)) == 
      GTExp(Pairing(g, h), ScalarMult(a, b))
  
  ghost predicate ValidSchnorrProof(
    nizk: SchnorrProof,
    statement: G1
  )
  {
    var c := HashToScalar([nizk.commitment, statement]);
    && nizk.challenge == c
    && G1Mult(G1Generator(), nizk.response) == 
       G1Add(nizk.commitment, G1Mult(statement, nizk.challenge))
  }
  
  lemma {:axiom} SchnorrSoundness(nizk: SchnorrProof, statement: G1)
    requires ValidSchnorrProof(nizk, statement)
    ensures exists w: Scalar :: 
      G1Mult(G1Generator(), w) == statement
  
  method VerifySchnorrProof(
    nizk: SchnorrProof,
    statement: G1
  ) returns (valid: bool)
    ensures valid <==> ValidSchnorrProof(nizk, statement)
  {
    var c := HashToScalar([nizk.commitment, statement]);
    if nizk.challenge != c {
      return false;
    }
    
    var lhs := G1Mult(G1Generator(), nizk.response);
    var rhs := G1Add(nizk.commitment, G1Mult(statement, nizk.challenge));
    return lhs == rhs;
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
    
    if pairingLHS != pairingRHS {
      return false;
    }
    
    var schnorrValid := VerifySchnorrProof(nizk, share);
    return schnorrValid;
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
      
      if !shareValid {
        return false;
      }
      
      i := i + 1;
    }
    
    return true;
  }
  
  ghost predicate ValidBBSignature(sig: G1, message: Fr, pk: G2)
  {
    Pairing(sig, G2Generator()) == Pairing(HashToG1(message), pk)
  }
  
  method VerifyBBSig(sig: G1, message: Fr, pk: G2) returns (valid: bool)
    ensures valid <==> ValidBBSignature(sig, message, pk)
  {
    var lhs := Pairing(sig, G2Generator());
    var rhs := Pairing(HashToG1(message), pk);
    return lhs == rhs;
  }
  
  method VerifyAllBBSignatures(
    signatures: seq<BBSignature>,
    candidateSet: seq<Fr>,
    verifierPK: G2
  ) returns (valid: bool)
    requires |signatures| == |candidateSet|
    ensures valid ==> 
      forall i :: 0 <= i < |candidateSet| ==>
        ValidBBSignature(signatures[i].sig, candidateSet[i], verifierPK)
  {
    var i := 0;
    while i < |candidateSet|
      invariant 0 <= i <= |candidateSet|
      invariant forall k :: 0 <= k < i ==>
        ValidBBSignature(signatures[k].sig, candidateSet[k], verifierPK)
    {
      var sigValid := VerifyBBSig(
        signatures[i].sig,
        candidateSet[i],
        verifierPK
      );
      
      if !sigValid {
        return false;
      }
      
      i := i + 1;
    }
    
    return true;
  }
  
  method CheckBlindedSigMatch(
    blindedSig: G1,
    bbSignatures: seq<BBSignature>
  ) returns (found: bool)
    ensures found ==> 
      exists i :: 0 <= i < |bbSignatures| && 
      bbSignatures[i].sig == blindedSig
  {
    found := false;
    var i := 0;
    while i < |bbSignatures|
      invariant 0 <= i <= |bbSignatures|
      invariant found ==> 
        exists k :: 0 <= k < |bbSignatures| && 
        bbSignatures[k].sig == blindedSig
    {
      if bbSignatures[i].sig == blindedSig {
        found := true;
        return true;
      }
      i := i + 1;
    }
    return false;
  }
  
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
    && (forall i :: 0 <= i < |candidateSet| ==>
          ValidBBSignature(proof.bbSignatures[i].sig, candidateSet[i], verifierPK))
    && ValidDistributedZKProof(proof.distributedProof, ciphertext, |serverPKs|, serverPKs)
    && (exists i :: 0 <= i < |proof.bbSignatures| &&
          proof.bbSignatures[i].sig == proof.blindedSig)
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
    if |proof.bbSignatures| != |candidateSet| {
      return false;
    }
    
    var bbSigsValid := VerifyAllBBSignatures(
      proof.bbSignatures,
      candidateSet,
      verifierPK
    );
    
    if !bbSigsValid {
      return false;
    }
    
    var dzkValid := VerifyDistributedZK(
      proof.distributedProof,
      ciphertext,
      serverPKs
    );
    
    if !dzkValid {
      return false;
    }
    
    var matchFound := CheckBlindedSigMatch(
      proof.blindedSig,
      proof.bbSignatures
    );
    
    return matchFound;
  }
  
  lemma {:axiom} TraceInSoundness(
    sk: SecretKey,
    c: Ciphertext,
    candidateSet: seq<Fr>,
    proof: TraceInProof,
    verifierPK: G2,
    serverPKs: seq<G2>
  )
    requires ValidTraceInProof(c, candidateSet, proof, verifierPK, serverPKs)
    ensures exists i :: 0 <= i < |candidateSet| && 
            Decrypt(sk, c) == candidateSet[i]
  
  method TraceIn(
    ciphertext: Ciphertext,
    candidateSet: seq<Fr>,
    proof: TraceInProof,
    verifierPK: G2,
    serverPKs: seq<G2>,
    ghost sk: SecretKey
  ) returns (found: bool)
    requires |serverPKs| >= 1
    ensures found ==> 
      exists i :: 0 <= i < |candidateSet| && 
      Decrypt(sk, ciphertext) == candidateSet[i]
  {
    var proofValid := VerifyTraceInProof(
      ciphertext,
      candidateSet,
      proof,
      verifierPK,
      serverPKs
    );
    
    if proofValid {
      TraceInSoundness(sk, ciphertext, candidateSet, proof, verifierPK, serverPKs);
      return true;
    }
    
    return false;
  }
  
  method BTraceIn(
    ciphertexts: seq<Ciphertext>,
    candidateSet: seq<Fr>,
    proofs: seq<TraceInProof>,
    verifierPK: G2,
    serverPKs: seq<G2>,
    ghost secretKeys: seq<SecretKey>
  ) returns (matchingCiphertexts: seq<Ciphertext>)
    requires |ciphertexts| == |proofs|
    requires |serverPKs| >= 1
    requires |secretKeys| == |serverPKs|
    ensures forall c :: c in matchingCiphertexts ==>
      exists i :: 0 <= i < |ciphertexts| && ciphertexts[i] == c &&
      exists j :: 0 <= j < |candidateSet| &&
      exists k :: 0 <= k < |secretKeys| &&
      Decrypt(secretKeys[k], c) == candidateSet[j]
  {
    matchingCiphertexts := [];
    
    var i := 0;
    while i < |ciphertexts|
      invariant 0 <= i <= |ciphertexts|
      invariant forall c :: c in matchingCiphertexts ==>
        exists idx :: 0 <= idx < i && ciphertexts[idx] == c &&
        exists j :: 0 <= j < |candidateSet| &&
        exists k :: 0 <= k < |secretKeys| &&
        Decrypt(secretKeys[k], c) == candidateSet[j]
    {
      var proofValid := VerifyTraceInProof(
        ciphertexts[i],
        candidateSet,
        proofs[i],
        verifierPK,
        serverPKs
      );
      
      if proofValid {
        TraceInSoundness(secretKeys[0], ciphertexts[i], candidateSet, proofs[i], verifierPK, serverPKs);
        matchingCiphertexts := matchingCiphertexts + [ciphertexts[i]];
      }
      
      i := i + 1;
    }
    
    return matchingCiphertexts;
  }
}
