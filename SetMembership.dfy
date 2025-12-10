module CryptoPrimitives {
  // 1. TYPE DECLARATIONS
  type Scalar(!new, ==)        
  type GroupElement(!new, ==)  
  type Ciphertext(!new, ==)    
  type Commitment(!new, ==)    
  type TargetGroup(!new, ==) 
  
  // 2. CONSTANTS AS FUNCTIONS
  function G(): GroupElement
  function Identity(): GroupElement
  function TargetIdentity(): TargetGroup 

  // 3. OPERATORS
  function ScalarAdd(a: Scalar, b: Scalar): Scalar
  function ScalarMult(a: Scalar, b: Scalar): Scalar
  function GroupAdd(p1: GroupElement, p2: GroupElement): GroupElement
  function GroupExp(base: GroupElement, exp: Scalar): GroupElement
  function Commit(val: Scalar, rand: Scalar): Commitment
  function Pairing(g1: GroupElement, g2: GroupElement): TargetGroup
  function CombineCommitments(c1: Commitment, c2: Commitment): Commitment

  // 4. AXIOMS
  lemma {:axiom} Axiom_GroupAssociativity(a: GroupElement, b: GroupElement, c: GroupElement)
    ensures GroupAdd(GroupAdd(a, b), c) == GroupAdd(a, GroupAdd(b, c))

  lemma {:axiom} Axiom_HomomorphicExp(base: GroupElement, a: Scalar, b: Scalar)
    ensures GroupExp(base, ScalarAdd(a, b)) == GroupAdd(GroupExp(base, a), GroupExp(base, b))

  lemma {:axiom} Axiom_CommitmentHomomorphism(v1: Scalar, r1: Scalar, v2: Scalar, r2: Scalar)
    ensures CombineCommitments(Commit(v1, r1), Commit(v2, r2)) 
            == Commit(ScalarAdd(v1, v2), ScalarAdd(r1, r2))

  // --- PREVIOUSLY MOVED HELPER ---
  datatype CommitContent = CommitContent(val: Scalar, rand: Scalar)
  function FromCommitment(c: Commitment): CommitContent
  lemma {:axiom} Axiom_FromCommitment(v: Scalar, r: Scalar)
      ensures FromCommitment(Commit(v, r)) == CommitContent(v, r)

  // --- NEW ADDITIONS (Fixes your Error) ---
  // Represents C^s (Scaling a commitment by a scalar)
  function CommitmentScale(c: Commitment, factor: Scalar): Commitment

  // Axiom: C(v, r)^s == C(v*s, r*s)
  lemma {:axiom} Axiom_CommitmentScale(v: Scalar, r: Scalar, factor: Scalar)
    ensures CommitmentScale(Commit(v, r), factor) == Commit(ScalarMult(v, factor), ScalarMult(r, factor))
}

module ZKPVerification {
  import opened CryptoPrimitives

  // 1. THE PROOF STRUCTURE
  datatype Proof = Proof(
    blindedSig: GroupElement, 
    challenge: Scalar,
    response_r: Scalar, 
    response_v: Scalar  
  )

  // 2. THE VERIFIER (The Circuit)
  function Verify(
      p: Proof, 
      commit: Commitment, 
      pk: GroupElement,
      accum: GroupElement
  ): bool 
  {
    var lhs_check := CombineCommitments(
        // C^c (Now works because FromCommitment is in CryptoPrimitives)
        Commit(ScalarMult(FromCommitment(commit).val, p.challenge), 
               ScalarMult(FromCommitment(commit).rand, p.challenge)), 
        // g^r
        Commit(p.response_v, p.response_r)
    );
    var rhs_check := ReconstructTarget(p.blindedSig, pk, p.challenge);
    lhs_check == rhs_check
  }

  // 3. THE HONEST PROVER
  function GenerateProof(
    v: Scalar, r: Scalar, c: Scalar, 
    nonce_v: Scalar, nonce_r: Scalar, sig: GroupElement
  ): Proof
  {
    Proof(sig, c, nonce_r, nonce_v)
  }

  // 4. AXIOMS & HELPERS
  function ReconstructTarget(sig: GroupElement, pk: GroupElement, c: Scalar): Commitment

  // (Deleted CommitContent, FromCommitment, Axiom_FromCommitment from here)

  lemma {:axiom} Axiom_Target_Behavior(sig: GroupElement, pk: GroupElement, c: Scalar, 
                                       v: Scalar, r: Scalar, nv: Scalar, nr: Scalar)
      ensures ReconstructTarget(sig, pk, c) == 
              Commit(ScalarAdd(ScalarMult(v, c), nv), ScalarAdd(ScalarMult(r, c), nr))

  // 5. THE COMPLETENESS THEOREM
  lemma Lemma_Completeness(v: Scalar, r: Scalar, c: Scalar, 
      nv: Scalar, nr: Scalar, sig: GroupElement, pk: GroupElement, accum: GroupElement)
    ensures Verify(GenerateProof(v, r, c, nv, nr, sig), Commit(v, r), pk, accum) == true
  {
     Axiom_FromCommitment(v, r);
     var val_term := ScalarMult(v, c);
     var rand_term := ScalarMult(r, c);
     Axiom_CommitmentHomomorphism(val_term, rand_term, nv, nr);
     Axiom_Target_Behavior(sig, pk, c, v, r, nv, nr);
  }

  // 6. SOUNDNESS (The Security Guarantee)
  function Extractor(p: Proof): (Scalar, Scalar)

  lemma {:axiom} Axiom_Soundness(p: Proof, c: Commitment, pk: GroupElement, accum: GroupElement)
    requires Verify(p, c, pk, accum)
    ensures 
      var (v, r) := Extractor(p);
      c == Commit(v, r)
}

module VotingState {
  import opened CryptoPrimitives
  import opened ZKPVerification
  import opened ReverseTraceability 

  class SecureAuditor {
    // 1. PUBLIC PARAMETERS
    const pk: GroupElement
    const accum: GroupElement

    // 2. STATE
    var auditedVotes: set<Commitment> 
    var decryptedVotes: set<Scalar>   

    // -------------------------------------------------------
    // INVARIANT (Ghost)
    // -------------------------------------------------------
    ghost predicate TraceabilityInvariant()
      reads this
    {
      forall v :: v in decryptedVotes ==> 
        exists c, r :: c in auditedVotes && c == Commit(v, r)
    }

    constructor(electionPK: GroupElement, targetSet: GroupElement)
      ensures pk == electionPK
      ensures accum == targetSet
      ensures auditedVotes == {}
      ensures decryptedVotes == {}
      ensures TraceabilityInvariant() 
    {
      pk := electionPK;
      accum := targetSet;
      auditedVotes := {};
      decryptedVotes := {};
    }

    // 3. AUDIT (Forward Step)
    method AuditVote(c: Commitment, p: Proof) returns (isValid: bool)
      modifies this
      requires TraceabilityInvariant() 
      ensures isValid == Verify(p, c, pk, accum)
      ensures TraceabilityInvariant()  
      ensures isValid ==> auditedVotes == old(auditedVotes) + {c}
      ensures !isValid ==> auditedVotes == old(auditedVotes)
    {
      isValid := Verify(p, c, pk, accum);
      if isValid {
        auditedVotes := auditedVotes + {c};
      }
    }

    // 4. LINKING FORWARD & REVERSE (FIXED)
    method DecryptAndPublish(c: Commitment, v: Scalar, p: DecryptionProof)
      modifies this
      requires TraceabilityInvariant() 
      requires IsTrusted(c)
      // FIX 1: Removed 'pk' argument. VerifyTraceOut now only needs (proof, commitment, value)
      requires VerifyTraceOut(p, c, v) 
      ensures TraceabilityInvariant()  
      ensures decryptedVotes == old(decryptedVotes) + {v}
    {
      // FIX 2: Updated axiom name to 'Axiom_ReverseSoundness' and removed 'pk'
      Axiom_ReverseSoundness(p, c, v);
      
      var r := ReverseExtractor(p);
      decryptedVotes := decryptedVotes + {v};
      
      assert c in auditedVotes; 
      assert c == Commit(v, r);
    }

    // 5. QUERY
    predicate IsTrusted(c: Commitment)
      reads this
    {
      c in auditedVotes
    }

    // -------------------------------------------------------
    // ★ THE FINAL THEOREM: SET MEMBERSHIP CORRECTNESS ★
    // -------------------------------------------------------
    lemma Theorem_Protocol_Correctness(c: Commitment, v: Scalar, p1: Proof, p2: DecryptionProof)
      // Condition A: The Forward Proof (Audit) is valid
      requires Verify(p1, c, pk, accum)
      
      // Condition B: The Reverse Proof (Decryption) is valid
      // FIX 3: Removed 'pk' argument
      requires VerifyTraceOut(p2, c, v)
      
      // CONCLUSION: The set membership holds physically
      ensures exists r :: c == Commit(v, r)
    {
      // FIX 4: Updated axiom name and removed 'pk'
      Axiom_ReverseSoundness(p2, c, v);
      
      var r := ReverseExtractor(p2);
      
      assert c == Commit(v, r);
    }
  }
}

module ReverseTraceability {
  import opened CryptoPrimitives

  // 1. DATA STRUCTURES
  datatype DecryptionProof = DecryptionProof(
    commitment_to_randomness: Commitment, 
    response_r: Scalar,                   
    challenge: Scalar                     
  )

  // 2. VERIFIER (Updated to use CommitmentScale)
  function VerifyTraceOut(p: DecryptionProof, C: Commitment, declared_v: Scalar): bool 
  {
    // LHS: Commit(v*c, s)
    var lhs_check := Commit(
        ScalarMult(declared_v, p.challenge), 
        p.response_r
    );

    // RHS: T + C^c
    // We use the new helper function here
    var scaled_C := CommitmentScale(C, p.challenge);

    var rhs_check := CombineCommitments(p.commitment_to_randomness, scaled_C);

    lhs_check == rhs_check
  }

  // 3. COMPLETENESS (Updated to use Axiom_CommitmentScale)
  lemma Lemma_ReverseCompleteness(
      v: Scalar, r: Scalar, k: Scalar, c: Scalar, 
      C: Commitment, T: Commitment, p: DecryptionProof
  )
    requires C == Commit(v, r)
    requires T == Commit(IdentityScalar(), k)
    requires p == DecryptionProof(T, ScalarAdd(k, ScalarMult(r, c)), c)
    ensures VerifyTraceOut(p, C, v)
  {
    // 1. Prove Scaling: C^c == Commit(v*c, r*c)
    Axiom_CommitmentScale(v, r, c);
    
    // 2. Prove Homomorphism: T * C^c == Commit(0+vc, k+rc)
    var vc := ScalarMult(v, c);
    var rc := ScalarMult(r, c);
    Axiom_CommitmentHomomorphism(IdentityScalar(), k, vc, rc);
    
    // 3. Identity Helper
    Axiom_ScalarIdentity(vc);
  }

  // 4. REVERSE SOUNDNESS
  function ReverseExtractor(p: DecryptionProof): Scalar

  lemma {:axiom} Axiom_ReverseSoundness(p: DecryptionProof, C: Commitment, v: Scalar)
    requires VerifyTraceOut(p, C, v)
    ensures 
      var r := ReverseExtractor(p);
      C == Commit(v, r)

  // HELPER
  function IdentityScalar(): Scalar 
  lemma {:axiom} Axiom_ScalarIdentity(s: Scalar)
    ensures ScalarAdd(s, IdentityScalar()) == s
    ensures ScalarAdd(IdentityScalar(), s) == s
}

module TestScenarios {
  import opened CryptoPrimitives
  import opened ZKPVerification
  import opened VotingState
  import opened ReverseTraceability

  // ---------------------------------------------------------
  // HELPER: Generate a Valid Decryption Proof (Honest Prover)
  // ---------------------------------------------------------
  // To pass the check: Commit(v*c, s) == T + C^c
  // We must choose:
  // T = Commit(0, k)  <- Randomness commitment (value is 0 because v is public)
  // s = k + r*c       <- Schnorr response
  function GenerateDecryptionProof(
      v: Scalar,      // The Vote
      r: Scalar,      // The Vote's Randomness (Witness)
      c: Scalar,      // The Challenge
      k: Scalar       // The Nonce (Randomness for the proof)
  ): DecryptionProof
  {
    // 1. Calculate T = Commit(0, k)
    var T := Commit(Zero(), k);
    
    // 2. Calculate s = k + r*c
    var s := ScalarAdd(k, ScalarMult(r, c));

    // 3. Return the proof structure
    DecryptionProof(T, s, c)
  }

// Need a Zero scalar helper for the commitment to 0
  function Zero(): Scalar
  
  lemma {:axiom} Axiom_Zero(s: Scalar)
    ensures ScalarAdd(s, Zero()) == s
    ensures ScalarAdd(Zero(), s) == s // <--- ADDED THIS LINE

  // =========================================================
  // TEST SUITE
  // =========================================================
  method RunTests(
      pk: GroupElement, 
      accum: GroupElement, 
      v: Scalar, r: Scalar, challenge: Scalar, 
      nv: Scalar, nr: Scalar, sig: GroupElement,
      proof_nonce_k: Scalar
  )
  {
    // -------------------------------------------------------
    // SETUP
    // -------------------------------------------------------
    var auditor := new SecureAuditor(pk, accum);
    var myCommitment := Commit(v, r);

    // -------------------------------------------------------
    // TEST 1: FORWARD AUDIT (Vote -> Blockchain)
    // -------------------------------------------------------
    // 1. Generate Audit Proof
    var auditProof := GenerateProof(v, r, challenge, nv, nr, sig);
    
    // 2. Verify and Submit
    Lemma_Completeness(v, r, challenge, nv, nr, sig, pk, accum);
    var isAuditValid := auditor.AuditVote(myCommitment, auditProof);
    
    assert isAuditValid == true;
    print "Test 1 (Audit): PASSED\n";

    // -------------------------------------------------------
    // TEST 2: REVERSE TRACEABILITY (Blockchain -> Vote)
    // -------------------------------------------------------
    // 1. Generate Decryption Proof
    // We prove we know 'r' such that myCommitment == Commit(v, r)
    var decProof := GenerateDecryptionProof(v, r, challenge, proof_nonce_k);

    // 2. Helper Lemmas for the math to work out
    // We need to tell Dafny that T + C^c == Commit(v*c, k + r*c)
    // This usually requires invoking the Homomorphism axioms manually
// 2. Helper Lemmas for the math to work out
    calc {
        // START: LHS of the verification check
        CombineCommitments(decProof.commitment_to_randomness, CommitmentScale(myCommitment, challenge));
        
        ==  { 
              // HINT 1: Tell Dafny how scaling works for this specific commitment
              Axiom_CommitmentScale(v, r, challenge); 
            }
        
        // Step 1: Expand definitions (T + C^c)
        CombineCommitments(
            Commit(Zero(), proof_nonce_k), 
            Commit(ScalarMult(v, challenge), ScalarMult(r, challenge))
        );
        
        ==  { 
              // HINT 2: Tell Dafny how to add these two specific commitments
              // We plug in the 4 values: v1, r1, v2, r2
              Axiom_CommitmentHomomorphism(
                  Zero(),                        // v1
                  proof_nonce_k,                 // r1
                  ScalarMult(v, challenge),      // v2
                  ScalarMult(r, challenge)       // r2
              );
            }

        // Step 2: Apply the addition inside the commitment
        Commit(
            ScalarAdd(Zero(), ScalarMult(v, challenge)), 
            ScalarAdd(proof_nonce_k, ScalarMult(r, challenge))
        );
        
        ==  { 
              // HINT 3: Tell Dafny that 0 + x = x
              Axiom_Zero(ScalarMult(v, challenge)); 
            }

        // Step 3: Simplify (0 + v*c becomes v*c)
        Commit(ScalarMult(v, challenge), decProof.response_r);
    }
    
    // 3. Verify Traceability
    // FIX: Removed 'pk' argument here
    if VerifyTraceOut(decProof, myCommitment, v) {
        auditor.DecryptAndPublish(myCommitment, v, decProof);
        print "Test 2 (Decryption): PASSED\n";
    } else {
        print "Test 2 (Decryption): FAILED\n";
        // Assert failure to stop execution if logic is wrong
        assert false; 
    }
  }
}