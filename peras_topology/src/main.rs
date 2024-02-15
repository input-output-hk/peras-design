use peras_topology::network::*;
use peras_topology::parameters::*;
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;

static PARAMETERS_YAML: &str = "
randomSeed: 12345
endSlot: 100
peerCount: 10
downstreamCount: 3
totalStake: null
maximumStake: 1000
messageDelay: 0.35
";

fn main() {
    let parameters: Parameters = serde_yaml::from_str(PARAMETERS_YAML).unwrap();
    println!(
        "PARAMETERS: {}",
        serde_json::to_string(&parameters).unwrap()
    );

    let rng = &mut ChaCha8Rng::seed_from_u64(parameters.randomSeed);

    let t = random_topology(rng, &parameters);
    println!("TOPOLOGY: {}", serde_json::to_string(&t).unwrap());
}
