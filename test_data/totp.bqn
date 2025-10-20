# XXX The whole implementation uses bit-vectors instead of calling •bit,
# because I wanted to stay sane while writing this.

# Number n to base b with minimal length p. If p is a function, it is called
# with the result vector as its argument to decide upon a length.
TB ⇐ { b‿p 𝕊 n: n{ 0𝕊r: r«(P r)⥊0; x𝕊r: (⌊x÷b) 𝕊 r∾˜b|x }⟨⟩ }
XOR ← ≠
HtB ← { 2‿32 TB 16⊸×⊸+˜´⌽(∾"0A"+⟜↕¨10‿6)⊐𝕩 } # Hex to bit

SHA1 ⇐ { # https://datatracker.ietf.org/doc/html/rfc3174
  ms ← 𝕩

  F ← { # f(t; B, C, D)
    t 𝕊 ⟨b,c,d⟩: t≤19? (d∧¬b) ∨ b∧c       ;
    t 𝕊 ⟨b,c,d⟩: t≤39? d XOR c XOR b      ;
    t 𝕊 ⟨b,c,d⟩: t≤59? (d∧c) ∨ (d∧b) ∨ c∧b;
    t 𝕊 ⟨b,c,d⟩: t≤79? d XOR c XOR b
  }
  K ← { # K(t)
    𝕩≤19? HtB "5A827999";
    𝕩≤39? HtB "6ED9EBA1";
    𝕩≤59? HtB "8F1BBCDC";
    𝕩≤79? HtB "CA62C1D6"
  }
  S ← ⌽                           # Circular shift S
  P ← 32‿1•bit._add⌾⌽             # Adding bit vectors

  # Method 1 in the RFC
  ms ∾↩ 1 ∾ ((512|-l+65)⥊0) ∾ 2‿64 TB (l←≠ms) # Pad to multiples of 512
  hs ← HtB¨ ⟨"67452301","EFCDAB89","98BADCFE","10325476","C3D2E1F0"⟩
  { ws ← 𝕩
    W  ← {𝕩⊏ws} # Block important here
    {ws ∾↩ 1 S (W𝕩-16) XOR (W𝕩-14) XOR (W𝕩-8) XOR (W𝕩-3) ⋄@}¨16+↕64
    ⟨a,b,c,d,e⟩ ← hs
    {temp ← (K𝕩) P (W𝕩) P e P (𝕩 F b‿c‿d) P (5 S a)
     e↩d ⋄ d↩c ⋄ c↩30 S b ⋄ b↩a ⋄ a↩temp ⋄@}¨↕80
    hs P¨↩ ⟨a,b,c,d,e⟩
    @
  }˘ ∘‿16‿32⥊ms # Groups of 16 words: M(1) to M(n)
  ∾hs # Result as binary string
}

HMAC ⇐ { k 𝕊 text: # https://datatracker.ietf.org/doc/html/rfc2104
  "HMAC: key should not exceed block length of SHA1" ! 512≥≠k
  k ↩ 512↑k                # Pad to 64 bytes
  P ← { ∾ 64⥊ < 24↓ HtB𝕩 } # ipad and opad
  SHA1 (k XOR P"5C") ∾ SHA1 (k XOR P"36")∾text
}

B32d ⇐ { # Base32 decoding; https://datatracker.ietf.org/doc/html/rfc4648
  ∾˝ ⌊‿8⥊ ∾ 2‿5⊸TB∘(⊑(('A'+↕26)∾'0'+2+↕6)⊸⊐)¨ '='⊸≠⊸/ 𝕩
  # To binary in 5-bit slices, then to bytes and drop excess.
}

HOTP ⇐ { k 𝕊 c: # https://datatracker.ietf.org/doc/html/rfc4226
  hm ← (B32d k) HMAC 2‿64 TB c
  # Turn low-order 4-bits to number n and then take the bytes hm[n] to
  # hm[n+3], keeping in mind hm has a flat representation.
  p  ← (8×2⊸×⊸+˜´⌽¯4↑hm)+↕8×4
  r  ← (10⋆6)| 2⊸×⊸+˜´⌽ 1↓ p⊏hm # Take last 31 bits only.
  '0'+ 10‿6 TB r
}

TOTP ⇐ { # https://datatracker.ietf.org/doc/html/rfc6238
  𝕩 HOTP ⌊30÷˜•UnixTime@
}
