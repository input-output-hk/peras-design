use serde::{Deserialize, Serialize};

#[derive(Eq, Clone, PartialEq, Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct Hash {
    #[serde(with = "hex::serde")]
    pub hash: [u8; 8],
}

#[derive(Eq, Clone, PartialEq, Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct LeadershipProof {
    #[serde(with = "hex::serde")]
    pub proof: [u8; 8],
}

#[derive(Eq, Clone, PartialEq, Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct MembershipProof {
    #[serde(with = "hex::serde")]
    pub proof: [u8; 8],
}

#[derive(Eq, Clone, PartialEq, Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct Signature {
    #[serde(with = "hex::serde")]
    pub signature: [u8; 8],
}
