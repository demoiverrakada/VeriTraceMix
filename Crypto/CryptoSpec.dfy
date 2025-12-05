module VeriTraceMix.CryptoSpec {

  datatype Message = Message(v: int)

  datatype Cipher = Cipher(enc: int, tag: int)

  type Key
  type TraceKey

  function Encrypt(m: Message, k: Key): Cipher

  function ReEncrypt(c: Cipher, k: Key): Cipher

  function Trace(c: Cipher, tk: TraceKey): int

  ghost predicate EncryptInjective(k: Key)
  {
    forall m1, m2 :: Encrypt(m1, k).enc == Encrypt(m2, k).enc ==> m1 == m2
  }

  ghost predicate ReEncryptPreservesTag(c: Cipher, k: Key)
  {
    ReEncrypt(c, k).tag == c.tag
  }

  ghost predicate TraceCorrect(c: Cipher, tk: TraceKey)
  {
    Trace(c, tk) == c.tag
  }

}
