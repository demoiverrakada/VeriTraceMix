// tv_primitives.dfy
module TVPrimitives {

  // Shared types
  type Scalar(==, !new)
  type G1(==, !new)
  type G2(==, !new)
  type GT(==, !new)
  type Fr(==, !new)

  type PublicKey = G2
  type SecretKey = Scalar

  // Shared ciphertext representation (must match both files)
  datatype Ciphertext = CT(c1: G1, c2: G1)

  // Shared primitives (union of what TraceIn + TraceOut reference)
  function G1Generator(): G1
  function G2Generator(): G2
  function IdentityG1(): G1

  function G1Add(a: G1, b: G1): G1
  function G1Sub(a: G1, b: G1): G1
  function G1Mult(g: G1, s: Scalar): G1

  function G2Mult(g: G2, s: Scalar): G2

  function Pairing(g1: G1, g2: G2): GT

  function HashToG1(m: Fr): G1
  function HashToScalar(data: seq<G1>): Scalar

  function ScalarAdd(a: Scalar, b: Scalar): Scalar
  function ScalarMult(a: Scalar, b: Scalar): Scalar
  function ScalarZero(): Scalar

  // One shared Decrypt (this is the key to type-sharing)
  ghost function Decrypt(sk: SecretKey, c: Ciphertext): Fr
}
