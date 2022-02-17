//! Global paramaters for the different Classic McEliece variants

use std::error;
use crate::randombytes::RNGState;

type R = Result<(), Box<dyn error::Error>>;


pub struct ClassicMcEliece<'t, const GFBITS: usize, const SYS_N: usize, const SYS_T: usize, const PK: usize, const SK: usize, const CT: usize>{
    /// Name of the variant
    pub primitive: &'t str,
}

impl<'t, const GF_SIZE: usize, const N: usize, const T: usize, const PK: usize, const SK: usize, const CT: usize> ClassicMcEliece<'t, GF_SIZE, N, T, PK, SK, CT> {
    pub const GFBITS: usize = GF_SIZE;
    pub const SYS_N: usize = N;
    pub const SYS_T: usize = T;

    pub const COND_BYTES: usize = (1 << (GF_SIZE - 4)) * (2 * GF_SIZE - 1);
    pub const IRR_BYTES: usize = T * 2;
    pub const PK_NROWS: usize = T * GF_SIZE;
    pub const PK_NCOLS: usize = N - Self::PK_NROWS;
    pub const PK_ROW_BYTES: usize = (Self::PK_NCOLS + 7) / 8;
    pub const SYND_BYTES: usize = (Self::PK_NROWS + 7) / 8;
    pub const GFMASK: usize = (1 << GF_SIZE) - 1;

    /// The number of bytes required to store the public key
    pub const PUBLICKEYBYTES: usize = PK;
    /// The number of bytes required to store the secret key
    pub const SECRETKEYBYTES: usize = SK;
    /// The number of bytes required to store the ciphertext resulting from the encryption
    pub const CIPHERTEXTBYTES: usize = CT;
    /// The number of bytes required to store the shared key (uniform among all variants)
    pub const CRYPTO_BYTES: usize = 32;

    /// KEM Keypair generation.
    ///
    /// Generate some public and secret key.
    /// The public key is meant to be shared with any party,
    /// but access to the secret key must be limited to the generating party.
    pub fn crypto_kem_keypair(&self, pk: &mut [u8], sk: &mut [u8], rng: &mut impl RNGState) -> R {
        assert_eq!(pk.len(), Self::PUBLICKEYBYTES, "public key has invalid size");
        assert_eq!(sk.len(), Self::SECRETKEYBYTES, "secret key has invalid size");

        Ok(())
    }

    /// KEM Encapsulation.
    ///
    /// Given a public key `pk`, sample a shared key.
    /// This shared key is returned through parameter `key` whereas
    /// the ciphertext (meant to be used for decapsulation) is returned as `c`.
    pub fn crypto_kem_enc(&self, c: &mut [u8], key: &mut [u8], pk: &[u8], rng: &mut impl RNGState) -> R {
        assert_eq!(pk.len(), Self::PUBLICKEYBYTES, "public key has invalid size");
        assert_eq!(key.len(), Self::CRYPTO_BYTES, "shared key has invalid size");
        assert_eq!(c.len(), Self::CIPHERTEXTBYTES, "ciphertext has invalid size");

        Ok(())
    }

    /// KEM Decapsulation.
    ///
    /// Given a secret key `sk` and a ciphertext `c`,
    /// determine the shared text `key` negotiated by both parties.
    pub fn crypto_kem_dec(&self, key: &mut [u8], c: &[u8], sk: &[u8]) -> R {
        assert_eq!(sk.len(), Self::SECRETKEYBYTES, "secret key has invalid size");
        assert_eq!(c.len(), Self::CIPHERTEXTBYTES, "ciphertext has invalid size");
        assert_eq!(key.len(), Self::CRYPTO_BYTES, "shared key has invalid size");

        Ok(())
    }
}

mod mceliece348864 {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 12;
    const SYS_N: usize = 3488;
    const SYS_T: usize = 64;
    const PUBLICKEYBYTES: usize = 261120;
    const SECRETKEYBYTES: usize = 6492;
    const CIPHERTEXTBYTES: usize = 128;
    const PRIMITIVE: &str = "mceliece348864";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}

mod mceliece348864f {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 12;
    const SYS_N: usize = 3488;
    const SYS_T: usize = 64;
    const PUBLICKEYBYTES: usize = 261120;
    const SECRETKEYBYTES: usize = 6492;
    const CIPHERTEXTBYTES: usize = 128;
    const PRIMITIVE: &str = "mceliece348864f";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}

mod mceliece460896 {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 13;
    const SYS_N: usize = 4608;
    const SYS_T: usize = 96;
    const PUBLICKEYBYTES: usize = 524160;
    const SECRETKEYBYTES: usize = 13608;
    const CIPHERTEXTBYTES: usize = 188;
    const PRIMITIVE: &str = "mceliece460896";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}

mod mceliece460896f {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 13;
    const SYS_N: usize = 4608;
    const SYS_T: usize = 96;
    const PUBLICKEYBYTES: usize = 524160;
    const SECRETKEYBYTES: usize = 13608;
    const CIPHERTEXTBYTES: usize = 188;
    const PRIMITIVE: &str = "mceliece460896f";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}

mod mceliece6688128 {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 13;
    const SYS_N: usize = 6688;
    const SYS_T: usize = 128;
    const PUBLICKEYBYTES: usize = 1044992;
    const SECRETKEYBYTES: usize = 13932;
    const CIPHERTEXTBYTES: usize = 240;
    const PRIMITIVE: &str = "mceliece6688128";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}

mod mceliece6688128f {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 13;
    const SYS_N: usize = 6688;
    const SYS_T: usize = 128;
    const PUBLICKEYBYTES: usize = 1044992;
    const SECRETKEYBYTES: usize = 13932;
    const CIPHERTEXTBYTES: usize = 240;
    const PRIMITIVE: &str = "mceliece6688128f";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}

mod mceliece6960119 {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 13;
    const SYS_N: usize = 6960;
    const SYS_T: usize = 119;
    const PUBLICKEYBYTES: usize = 1047319;
    const SECRETKEYBYTES: usize = 13948;
    const CIPHERTEXTBYTES: usize = 226;
    const PRIMITIVE: &str = "mceliece6960119";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}

mod mceliece6960119f {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 13;
    const SYS_N: usize = 6960;
    const SYS_T: usize = 119;
    const PUBLICKEYBYTES: usize = 1047319;
    const SECRETKEYBYTES: usize = 13948;
    const CIPHERTEXTBYTES: usize = 226;
    const PRIMITIVE: &str = "mceliece6960119f";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}

mod mceliece8192128 {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 13;
    const SYS_N: usize = 8192;
    const SYS_T: usize = 128;
    const PUBLICKEYBYTES: usize = 1357824;
    const SECRETKEYBYTES: usize = 14120;
    const CIPHERTEXTBYTES: usize = 240;
    const PRIMITIVE: &str = "mceliece8192128";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}

mod mceliece8192128f {
    use crate::ClassicMcEliece;

    const GFBITS: usize = 13;
    const SYS_N: usize = 8192;
    const SYS_T: usize = 128;
    const PUBLICKEYBYTES: usize = 1357824;
    const SECRETKEYBYTES: usize = 14120;
    const CIPHERTEXTBYTES: usize = 240;
    const PRIMITIVE: &str = "mceliece8192128f";
    const KEM: ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES> = ClassicMcEliece::<'static, GFBITS, SYS_N, SYS_T, PUBLICKEYBYTES, SECRETKEYBYTES, CIPHERTEXTBYTES>{ primitive: PRIMITIVE };
}
