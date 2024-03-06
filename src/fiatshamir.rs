use ark_ff::PrimeField;
use merlin::Transcript;

pub trait ProtocolTranscript<F: PrimeField> {
    fn append_scalar(&mut self, label: &'static [u8], scalar: &F);
    fn append_message(&mut self, label: &'static [u8], message: &'static [u8]);
    fn append_points(&mut self, label: &'static [u8], points: &[F]);
    fn challenge_scalar(&mut self, label: &'static [u8]) -> F;
    fn challenge_scalars(&mut self, label: &'static [u8], count: usize) -> Vec<F>;
}

impl<F: PrimeField> ProtocolTranscript<F> for Transcript {
    fn append_scalar(&mut self, label: &'static [u8], scalar: &F) {
        let mut buf: Vec<u8> = vec![];
        scalar.serialize_compressed(&mut buf).unwrap();
        self.append_message(label, &buf);
    }

    fn append_message(&mut self, label: &'static [u8], msg: &'static [u8]) {
        self.append_message(label, msg);
    }

    fn append_points(&mut self, label: &'static [u8], points: &[F]) {
        self.append_message(label, b"begin_append_points");
        for item in points.iter() {
            self.append_scalar(label, item);
        }
        self.append_message(label, b"end_append_points");
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> F {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        F::from_le_bytes_mod_order(&buf)
    }

    fn challenge_scalars(&mut self, label: &'static [u8], count: usize) -> Vec<F> {
        (0..count).map(|_| self.challenge_scalar(label)).collect()
    }
}

trait Provable<F: PrimeField> {
    fn prove(&self, transcript: impl ProtocolTranscript<F>);
    fn verify(&self, transcript: impl ProtocolTranscript<F>) -> bool;
}
