import Solutions
/-!
# Proved tasks

One theorem per proved task, and nothing else: the theorem is named `Claims.<task>` and its type is
the task's proposition, written as that single constant. The proof is a reference into `Solutions`.

    theorem Claims.ChaCha20_ctr32_correct : Ssl.OpensslChacha20.ChaCha20_ctr32_correct :=
      Solutions.…

`Audit.lean` reads this file: a task without a theorem here is open.
-/

theorem Claims.Poly1305_ctx_size_correct : Ssl.OpensslPoly1305.Poly1305_ctx_size_correct :=
  Solutions.OpensslPoly1305.ctx_size_correct

theorem Claims.fe_add_correct : Ssl.OpensslX25519.fe_add_correct :=
  Solutions.OpensslX25519.fe_add_ok

theorem Claims.fe_sub_correct : Ssl.OpensslX25519.fe_sub_correct :=
  Solutions.OpensslX25519.fe_sub_ok

theorem Claims.fe_sq_correct : Ssl.OpensslX25519.fe_sq_correct :=
  Solutions.OpensslX25519.fe_sq_ok

theorem Claims.fe_mul_correct : Ssl.OpensslX25519.fe_mul_correct :=
  Solutions.OpensslX25519.fe_mul_ok

theorem Claims.ChaCha20_ctr32_correct : Ssl.OpensslChacha20.ChaCha20_ctr32_correct :=
  Solutions.OpensslChacha20.ChaCha20_ctr32_correct

theorem Claims.sha256_streaming_correct : Ssl.OpensslSha256.sha256_streaming_correct :=
  Solutions.OpensslSha256.sha256_streaming_ok

theorem Claims.sha224_streaming_correct : Ssl.OpensslSha256.sha224_streaming_correct :=
  Solutions.OpensslSha256.sha224_streaming_ok

theorem Claims.SHA256_Transform_correct : Ssl.OpensslSha256.SHA256_Transform_correct :=
  Solutions.OpensslSha256.transform_correct

theorem Claims.Poly1305_correct : Ssl.OpensslPoly1305.Poly1305_correct :=
  Solutions.OpensslPoly1305.Poly1305_correct_ok

theorem Claims.Poly1305_oneshot : Ssl.OpensslPoly1305.Poly1305_oneshot :=
  Solutions.OpensslPoly1305.Poly1305_oneshot_ok

theorem Claims.ossl_x25519_correct : Ssl.OpensslX25519.ossl_x25519_correct :=
  Solutions.OpensslX25519.ossl_x25519_ok
