// Crypto/CryptoSpec.dfy
// Cryptographic specifications for the traceable mixnet

module CryptoSpec {
  
  // Abstract types for cryptographic objects
  type PublicKey
  type SecretKey
  type Ciphertext
  type Plaintext
  type Randomness
  
  // Key pair generation
  ghost predicate ValidKeyPair(pk: PublicKey, sk: SecretKey)
  
  // Encryption function
  ghost function Encrypt(pk: PublicKey, m: Plaintext, r: Randomness): Ciphertext
  
  // Decryption function
  ghost function Decrypt(sk: SecretKey, c: Ciphertext): Plaintext
    requires exists pk :: ValidKeyPair(pk, sk)
  
  // Re-encryption: takes a ciphertext and produces a fresh ciphertext
  // of the same plaintext under the same public key
  ghost function ReEncrypt(pk: PublicKey, c: Ciphertext, r: Randomness): Ciphertext
  
  // Correctness of encryption/decryption
  lemma DecryptionCorrectness(pk: PublicKey, sk: SecretKey, m: Plaintext, r: Randomness)
    requires ValidKeyPair(pk, sk)
    ensures Decrypt(sk, Encrypt(pk, m, r)) == m
  
  // Re-encryption preserves plaintext
  lemma ReEncryptionCorrectness(pk: PublicKey, sk: SecretKey, c: Ciphertext, r: Randomness)
    requires ValidKeyPair(pk, sk)
    requires exists m, r0 :: c == Encrypt(pk, m, r0)
    ensures Decrypt(sk, ReEncrypt(pk, c, r)) == Decrypt(sk, c)
  
  // Homomorphic property (if needed for mixnet)
  // Can be extended based on the specific cryptosystem
  
  ghost predicate IsFreshRandomness(r: Randomness)
  
  // Two ciphertexts with different randomness are different
  lemma RandomnessGivesDistinctCiphertexts(pk: PublicKey, m: Plaintext, r1: Randomness, r2: Randomness)
    requires IsFreshRandomness(r1)
    requires IsFreshRandomness(r2)
    requires r1 != r2
    ensures Encrypt(pk, m, r1) != Encrypt(pk, m, r2)
}
