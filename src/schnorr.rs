use curve25519_dalek::{RistrettoPoint, Scalar};
use rand_core::OsRng;

pub fn commit(g: &RistrettoPoint) -> (Scalar, RistrettoPoint) {
    let alpha = Scalar::random(&mut OsRng);
    let t = alpha * g;
    (alpha, t)
}

pub fn random_challenge() -> Scalar
{
    Scalar::random(&mut OsRng)
}

pub fn respond(alpha: Scalar, beta: Scalar, x: Scalar) -> Scalar
{
    beta * x + alpha
}

pub fn check(
    g: &RistrettoPoint,
    p: &RistrettoPoint,
    t: &RistrettoPoint,
    beta: Scalar,
    z: Scalar,
) -> bool {
    z * g == t + beta * p
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::Sha512;

    fn base() -> RistrettoPoint {
        RistrettoPoint::hash_from_bytes::<Sha512>(b"schnorr/test/g")
    }

    #[test]
    fn honest_proof_verifies() {
        let g = base();
        let x = Scalar::random(&mut OsRng);
        let p = x * g;

        let (alpha, t) = commit(&g);
        let beta = random_challenge();
        let z = respond(alpha, beta, x);

        assert!(check(&g, &p, &t, beta, z));
    }

    #[test]
    fn wrong_secret_fails() {
        let g = base();
        let x = Scalar::random(&mut OsRng);
        let p = x * g;

        let (alpha, t) = commit(&g);
        let beta = random_challenge();
        let wrong = Scalar::random(&mut OsRng);
        let z = respond(alpha, beta, wrong);

        assert!(!check(&g, &p, &t, beta, z));
    }

    #[test]
    fn wrong_challenge_fails() {
        // A proof answered for one challenge does not satisfy another.
        let g = base();
        let x = Scalar::random(&mut OsRng);
        let p = x * g;

        let (alpha, t) = commit(&g);
        let beta = random_challenge();
        let z = respond(alpha, beta, x);

        assert!(!check(&g, &p, &t, random_challenge(), z));
    }

    #[test]
    fn simulator_produces_an_accepting_transcript() {
        // Zero-knowledge, made concrete: build a passing transcript
        // WITHOUT knowing x. Work backwards from the check.
        let g = base();
        let x = Scalar::random(&mut OsRng);
        let p = x * g;            // x is never used again below

        let z = Scalar::random(&mut OsRng);
        let beta = random_challenge();
        let t = z * g - beta * p;          // <- the simulator

        assert!(check(&g, &p, &t, beta, z));
    }

    #[test]
    fn extractor_recovers_the_secret() {
        // Special soundness, made concrete: two accepting transcripts sharing
        // the same t but with different challenges reveal x. This is the
        // extractor from Theorem 1(ii), in six lines.
        let g = base();
        let x = Scalar::random(&mut OsRng);

        let (alpha, _t) = commit(&g);
        let beta1 = random_challenge();
        let beta2 = random_challenge();
        let z1 = respond(alpha, beta1, x);
        let z2 = respond(alpha, beta2, x);

        // z1 - z2 = (beta1 - beta2) * x   =>   x = (z1 - z2)/(beta1 - beta2)
        let extracted = (z1 - z2) * (beta1 - beta2).invert();

        assert_eq!(extracted, x);
    }
}