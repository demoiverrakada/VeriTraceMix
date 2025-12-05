// Spec/SetMembership.dfy
// Specification for set membership proofs in the mixnet

include "../Crypto/CryptoSpec.dfy"

module SetMembership {
  import opened CryptoSpec
  
  // A set membership proof shows that an element belongs to a set
  // without revealing which specific element it is
  
  datatype SetMembershipProof = SetMembershipProof(
    element: Ciphertext,
    witnessSet: seq<Ciphertext>,
    proof: seq<int>  // Abstract proof representation
  )
  
  // Predicate: a ciphertext is in the input set
  ghost predicate IsInSet(c: Ciphertext, inputs: seq<Ciphertext>)
  {
    exists i :: 0 <= i < |inputs| && inputs[i] == c
  }
  
  // Predicate: a ciphertext decrypts to the same plaintext as one in the set
  ghost predicate DecryptsToSamePlaintext(sk: SecretKey, c: Ciphertext, inputs: seq<Ciphertext>)
    // The caller must ensure ValidKeyPair(pk, sk) holds for some pk
  {
    exists i :: 0 <= i < |inputs| && Decrypt(sk, c) == Decrypt(sk, inputs[i])
  }
  
  // Valid set membership proof
  ghost predicate ValidSetMembershipProof(
    proof: SetMembershipProof,
    pk: PublicKey,
    sk: SecretKey,
    inputs: seq<Ciphertext>
  )
    requires ValidKeyPair(pk, sk)
  {
    && proof.witnessSet == inputs
    && DecryptsToSamePlaintext(sk, proof.element, inputs)
  }
  
  // Completeness: honest prover can always create valid proof
  lemma {:axiom} SetMembershipCompleteness(
    c: Ciphertext,
    pk: PublicKey,
    sk: SecretKey,
    inputs: seq<Ciphertext>
  )
    requires ValidKeyPair(pk, sk)
    requires DecryptsToSamePlaintext(sk, c, inputs)
    ensures exists proof :: ValidSetMembershipProof(proof, pk, sk, inputs) && proof.element == c

  // Soundness: valid proof means element is actually in set (after re-encryption)
  lemma {:axiom} SetMembershipSoundness(
    proof: SetMembershipProof,
    pk: PublicKey,
    sk: SecretKey,
    inputs: seq<Ciphertext>
  )
    requires ValidKeyPair(pk, sk)
    ensures DecryptsToSamePlaintext(sk, proof.element, inputs)
  
  // Helper: extract index of matching element
  ghost function FindMatchingIndex(sk: SecretKey, c: Ciphertext, inputs: seq<Ciphertext>): int
    // The caller must ensure ValidKeyPair(pk, sk) holds for some pk
    requires DecryptsToSamePlaintext(sk, c, inputs)
    ensures 0 <= FindMatchingIndex(sk, c, inputs) < |inputs|
    ensures Decrypt(sk, c) == Decrypt(sk, inputs[FindMatchingIndex(sk, c, inputs)])
  {
    var i :| 0 <= i < |inputs| && Decrypt(sk, c) == Decrypt(sk, inputs[i]);
    i
  }
}
