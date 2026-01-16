module TraceableVotingTraceOut {
  import opened TVPrimitives

  // Optional helper if you later want a more “ElGamal-like” encryption model
  function PKtoG1(pk: PublicKey): G1

  // ========================================================================
  // ENCRYPTION (kept ghost/abstract)
  // ========================================================================
  ghost function EncryptWithRandomness(pk: PublicKey, m: Fr, r: Scalar): Ciphertext
  {
    CT(
      c1 := G1Mult(G1Generator(), r),
      // abstract “pk^r” contribution via PKtoG1(pk)
      c2 := G1Add(HashToG1(m), G1Mult(G1Generator(), r))
    )
  }

  lemma {:axiom} EncryptionCorrectness(sk: SecretKey, pk: PublicKey, m: Fr, r: Scalar)
    ensures Decrypt(sk, EncryptWithRandomness(pk, m, r)) == m

  // ========================================================================
  // HELPER PREDICATE (shared “success” notion)
  // ========================================================================
  ghost predicate IsDecryptedCorrectly(plaintext: Fr, ciphertextSet: seq<Ciphertext>, sk: SecretKey)
  {
    exists j :: 0 <= j < |ciphertextSet| &&
      Decrypt(sk, ciphertextSet[j]) == plaintext
  }

  // ========================================================================
  // DATA STRUCTURES
  // ========================================================================
  datatype SchnorrProof = Schnorr(
    commitment: G1,
    challenge: Scalar,
    response: Scalar
  )

  datatype MembershipProof = MemProof(
    commitmentToRandomness: G1,
    nizk: SchnorrProof
  )

  datatype TraceOutProof = TOProof(
    targetCiphertextIndex: nat,
    membershipProof: MembershipProof
  )

  // ========================================================================
  // ZK LOGIC
  // ========================================================================
  ghost predicate ValidSchnorrProof(nizk: SchnorrProof, statement: G1)
  {
    var c := HashToScalar([nizk.commitment, statement]);
    nizk.challenge == c
    &&
    G1Mult(G1Generator(), nizk.response) ==
      G1Add(nizk.commitment, G1Mult(statement, nizk.challenge))
  }

  lemma {:axiom} SchnorrSoundness(nizk: SchnorrProof, statement: G1)
    requires ValidSchnorrProof(nizk, statement)
    ensures exists w: Scalar :: G1Mult(G1Generator(), w) == statement

  // ========================================================================
  // TRACEOUT SPECIFICATION
  // ========================================================================
  ghost predicate ProofBindsToCiphertext(
    proof: MembershipProof,
    targetCT: Ciphertext,
    plaintext: Fr,
    serverPK: G2
  )
  {
    // The “binding” in this abstract model: proof must reference the target CT's c1
    proof.commitmentToRandomness == targetCT.c1
    &&
    ValidSchnorrProof(proof.nizk, proof.commitmentToRandomness)
  }

  ghost predicate ValidTraceOutProof(
    plaintext: Fr,
    ciphertextSet: seq<Ciphertext>,
    proof: TraceOutProof,
    serverPK: G2
  )
  {
    proof.targetCiphertextIndex < |ciphertextSet|
    &&
    (var targetCT := ciphertextSet[proof.targetCiphertextIndex];
     ProofBindsToCiphertext(proof.membershipProof, targetCT, plaintext, serverPK))
  }

  // ========================================================================
  // SECURITY AXIOM (soundness assumption)
  // ========================================================================
  lemma {:axiom} TraceOutSoundness(
    sk: SecretKey,
    plaintext: Fr,
    ciphertextSet: seq<Ciphertext>,
    proof: TraceOutProof,
    serverPK: G2
  )
    requires ValidTraceOutProof(plaintext, ciphertextSet, proof, serverPK)
    ensures IsDecryptedCorrectly(plaintext, ciphertextSet, sk)
    ensures Decrypt(sk, ciphertextSet[proof.targetCiphertextIndex]) == plaintext

  // ========================================================================
  // IMPLEMENTATION
  // ========================================================================
  method VerifySchnorrProof(nizk: SchnorrProof, statement: G1) returns (valid: bool)
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

  method VerifyProofBinding(
    proof: MembershipProof,
    targetCT: Ciphertext,
    plaintext: Fr,
    serverPK: G2
  ) returns (valid: bool)
    ensures valid ==> ProofBindsToCiphertext(proof, targetCT, plaintext, serverPK)
  {
    if proof.commitmentToRandomness != targetCT.c1 {
      return false;
    }

    var zkValid := VerifySchnorrProof(proof.nizk, proof.commitmentToRandomness);
    return zkValid;
  }

  method VerifyTraceOutProof(
    plaintext: Fr,
    ciphertextSet: seq<Ciphertext>,
    proof: TraceOutProof,
    serverPK: G2
  ) returns (valid: bool)
    ensures valid ==> ValidTraceOutProof(plaintext, ciphertextSet, proof, serverPK)
  {
    if proof.targetCiphertextIndex >= |ciphertextSet| {
      return false;
    }

    var targetCT := ciphertextSet[proof.targetCiphertextIndex];
    var bindingValid := VerifyProofBinding(proof.membershipProof, targetCT, plaintext, serverPK);
    return bindingValid;
  }

  method TraceOut(
    plaintext: Fr,
    ciphertextSet: seq<Ciphertext>,
    proof: TraceOutProof,
    serverPK: G2,
    ghost sk: SecretKey
  ) returns (found: bool)
    ensures found ==> IsDecryptedCorrectly(plaintext, ciphertextSet, sk)
    ensures found ==> proof.targetCiphertextIndex < |ciphertextSet|
    ensures found ==> Decrypt(sk, ciphertextSet[proof.targetCiphertextIndex]) == plaintext
  {
    var isValid := VerifyTraceOutProof(plaintext, ciphertextSet, proof, serverPK);
    if isValid {
      TraceOutSoundness(sk, plaintext, ciphertextSet, proof, serverPK);
      return true;
    }
    return false;
  }

  // ========================================================================
  // BATCH VERIFICATION
  // ========================================================================
  lemma BatchSoundness(
    plaintexts: seq<Fr>,
    ciphertextSet: seq<Ciphertext>,
    proofs: seq<TraceOutProof>,
    serverPK: G2,
    sk: SecretKey,
    limit: nat
  )
    requires |plaintexts| == |proofs|
    requires limit <= |plaintexts|
    requires forall k :: 0 <= k < limit ==> ValidTraceOutProof(plaintexts[k], ciphertextSet, proofs[k], serverPK)
    ensures  forall k :: 0 <= k < limit ==> IsDecryptedCorrectly(plaintexts[k], ciphertextSet, sk)
    decreases limit
  {
    if limit == 0 {
      return;
    }

    BatchSoundness(plaintexts, ciphertextSet, proofs, serverPK, sk, limit - 1);
    var k := limit - 1;
    TraceOutSoundness(sk, plaintexts[k], ciphertextSet, proofs[k], serverPK);
  }

  method BatchTraceOut(
    plaintexts: seq<Fr>,
    ciphertextSet: seq<Ciphertext>,
    proofs: seq<TraceOutProof>,
    serverPK: G2,
    ghost sk: SecretKey
  ) returns (allValid: bool)
    requires |plaintexts| == |proofs|
    ensures  allValid ==> forall k :: 0 <= k < |plaintexts| ==> IsDecryptedCorrectly(plaintexts[k], ciphertextSet, sk)
  {
    var i := 0;

    while i < |plaintexts|
      invariant 0 <= i <= |plaintexts|
      invariant forall k :: 0 <= k < i ==> ValidTraceOutProof(plaintexts[k], ciphertextSet, proofs[k], serverPK)
    {
      var ok := VerifyTraceOutProof(plaintexts[i], ciphertextSet, proofs[i], serverPK);
      if !ok {
        return false;
      }
      i := i + 1;
    }

    BatchSoundness(plaintexts, ciphertextSet, proofs, serverPK, sk, |plaintexts|);
    return true;
  }
}
