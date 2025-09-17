pub struct FiniteValuation<const N: usize, V>([Vec<V>; N]);

impl<const N: usize, V: Eq> FiniteValuation<N, V> {
    pub fn assignment(&self, world: usize, var: &V) -> bool {
        world < N && self.0[world].contains(var)
    }
}

impl<const N: usize, V: Clone> FiniteValuation<N, V> {
    pub fn all_valuations_varying(variables: Vec<V>) -> impl Iterator<Item = Self> {
        let var_count = variables.len();
        let total_valuations = 1 << (var_count * N);

        (0..total_valuations).map(move |num| {
            let mut assignment: [Vec<V>; N] = core::array::from_fn(|_| Vec::new());
            for world in 0..N {
                for (var_index, var) in variables.iter().enumerate() {
                    let bit_index = world * var_count + var_index;
                    if (num & (1 << bit_index)) != 0 {
                        assignment[world].push(var.clone());
                    }
                }
            }
            FiniteValuation(assignment)
        })
    }
}
