include "../Crypto/CryptoSpec.dfy"

module SetMembership {

  import opened CryptoSpec

  ghost predicate SetMembership(before: seq<Cipher>, after: seq<Cipher>, k: Key)
  {
    |before| == |after|
    &&
    forall j :: 0 <= j < |after| ==>
      exists i :: 0 <= i < |before| &&
        after[j] == ReEncrypt(before[i], k)
  }

  lemma SetMembershipLength(before: seq<Cipher>, after: seq<Cipher>, k: Key)
    requires SetMembership(before, after, k)
    ensures |before| == |after|
  {}
}
