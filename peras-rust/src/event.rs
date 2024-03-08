use serde::{Deserialize, Serialize};

#[derive(Eq, Clone, PartialEq, Serialize, Deserialize, Debug)]
#[serde(transparent, rename_all = "camelCase")]
pub struct UniqueId {
    #[serde(with = "hex::serde")]
    pub unique_id: [u8; 8],
}
