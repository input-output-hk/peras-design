use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct Hash {
    #[serde(with = "hex::serde")]
    hash: [u8; 8],
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct LeadershipProof {
    #[serde(with = "hex::serde")]
    proof: [u8; 8],
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct MembershipProof {
    #[serde(with = "hex::serde")]
    proof: [u8; 8],
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct Signature {
    #[serde(with = "hex::serde")]
    signature: [u8; 8],
}
