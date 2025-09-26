use itertools::Itertools;

use crate::formula::Formula;
use crate::valuation::FiniteValuation;
use std::collections::BTreeMap;
use std::sync::LazyLock;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FiniteKripkeFrame<const N: usize> {
    pub accessibility: [[bool; N]; N],
}

impl<const N: usize> FiniteKripkeFrame<N> {
    pub fn worlds_that_validate<V: Eq>(
        &self,
        formula: &Formula<V>,
        valuation: &FiniteValuation<N, V>,
    ) -> [bool; N] {
        match formula {
            Formula::Var(v) => {
                let mut result = [false; N];
                for i in 0..N {
                    result[i] = valuation.assignment(i, v);
                }
                result
            }
            Formula::True => [true; N],
            Formula::False => [false; N],
            Formula::Not(f) => {
                let mut sub_result = self.worlds_that_validate(f, valuation);
                for i in 0..N {
                    sub_result[i] = !sub_result[i];
                }
                sub_result
            }
            Formula::And(f1, f2) => {
                let mut sub_result1 = self.worlds_that_validate(f1, valuation);
                let sub_result2 = self.worlds_that_validate(f2, valuation);
                for i in 0..N {
                    sub_result1[i] &= sub_result2[i];
                }
                sub_result1
            }
            Formula::Or(f1, f2) => {
                let mut sub_result1 = self.worlds_that_validate(f1, valuation);
                let sub_result2 = self.worlds_that_validate(f2, valuation);
                for i in 0..N {
                    sub_result1[i] |= sub_result2[i];
                }
                sub_result1
            }
            Formula::Imp(f1, f2) => {
                let mut sub_result1 = self.worlds_that_validate(f1, valuation);
                let sub_result2 = self.worlds_that_validate(f2, valuation);
                for i in 0..N {
                    sub_result1[i] = !sub_result1[i] || sub_result2[i];
                }
                sub_result1
            }
            Formula::Iff(f1, f2) => {
                let mut sub_result1 = self.worlds_that_validate(f1, valuation);
                let sub_result2 = self.worlds_that_validate(f2, valuation);
                for i in 0..N {
                    sub_result1[i] = sub_result1[i] == sub_result2[i];
                }
                sub_result1
            }
            Formula::MBox(f) => {
                let sub_result = self.worlds_that_validate(f, valuation);
                let mut result = [false; N];
                for i in 0..N {
                    result[i] = (0..N).all(|j| !self.accessibility[i][j] || sub_result[j]);
                }
                result
            }
            Formula::MDia(f) => {
                let sub_result = self.worlds_that_validate(f, valuation);
                let mut result = [false; N];
                for i in 0..N {
                    result[i] = (0..N).any(|j| self.accessibility[i][j] && sub_result[j]);
                }
                result
            }
        }
    }

    pub fn worlds_that_validate_under_any_valuation<V: Eq + Clone>(
        &self,
        formula: &Formula<V>,
    ) -> [bool; N] {
        let variables = formula
            .variables_dedup()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();

        let mut result = [true; N];
        for valuation in FiniteValuation::<N, V>::all_valuations_varying(variables) {
            let validation_results = self.worlds_that_validate(formula, &valuation);
            for i in 0..N {
                result[i] &= validation_results[i];
            }
        }
        result
    }

    pub fn number_of_worlds_validating<V: Eq + Clone>(&self, formula: &Formula<V>) -> u8 {
        self.worlds_that_validate_under_any_valuation(formula)
            .into_iter()
            .filter(|&b| b)
            .count() as u8
    }

    pub fn accessibility_relation_count(&self) -> usize {
        let mut count = 0;
        for i in 0..N {
            for j in 0..N {
                if self.accessibility[i][j] {
                    count += 1;
                }
            }
        }
        count
    }
}

impl FiniteKripkeFrame<4> {
    pub fn to_u16_id(&self) -> u16 {
        let mut id = 0u16;
        for (i, j) in (0..4).cartesian_product(0..4) {
            if self.accessibility[i][j] {
                id |= 1 << (i * 4 + j);
            }
        }
        id
    }

    pub fn compute_from_u16_id(id: u16) -> Self {
        let mut accessibility = [[false; 4]; 4];
        for (i, j) in (0..4).cartesian_product(0..4) {
            accessibility[i][j] = (id & (1 << (i * 4 + j))) != 0;
        }
        FiniteKripkeFrame { accessibility }
    }

    pub fn empty_frame() -> Self {
        FiniteKripkeFrame {
            accessibility: [[false; 4]; 4],
        }
    }

    pub fn isomorphism_classes_with_possible_duplications(
        &self,
    ) -> impl Iterator<Item = FiniteKripkeFrame<4>> {
        vec![0usize, 1, 2, 3]
            .into_iter()
            .permutations(4)
            .map(move |perm| {
                let mut new_frame = FiniteKripkeFrame::empty_frame();
                for (i, j) in (0..4).cartesian_product(0..4) {
                    new_frame.accessibility[perm[i]][perm[j]] = self.accessibility[i][j];
                }
                new_frame
            })
    }

    pub fn all_ids_iter() -> impl Iterator<Item = u16> {
        (0u16..=0xFFFF).into_iter()
    }

    pub fn into_graphviz_dot_string(&self) -> String {
        format!(
            r#"strict digraph G {{ layout="fdp"; color="white"; node [label="", shape="circle"]; label="{}"; v0 [pos="0,0!"]; v1[pos="2,0!"]; v2 [pos="0,-2!"]; v3 [pos="2,-2!"]; {} }}"#,
            self.to_u16_id(),
            // edges
            (0..4)
                .cartesian_product(0..4)
                .filter(|(i, j)| self.accessibility[*i][*j])
                .map(|(i, j)| {
                    if i == j {
                        if i == 0 || i == 2 {
                            format!("v{}:nw->v{}:sw;", i, j)
                        } else {
                            format!("v{}:ne->v{}:se;", i, j)
                        }
                    } else {
                        format!("v{}->v{};", i, j)
                    }
                })
                .join(" ")
        )
    }

    pub const ALL_FRAMES_COUNT: usize = 65536;

    // https://oeis.org/A000595
    pub const NO_OF_FRAMES_UPTO_ISOMORPHISM: usize = 3044;

    pub fn from_u16_id(id: u16) -> &'static FiniteKripkeFrame<4> {
        static CACHE: LazyLock<Vec<FiniteKripkeFrame<4>>> = LazyLock::new(|| {
            let mut vec = Vec::with_capacity(FiniteKripkeFrame::<4>::ALL_FRAMES_COUNT);
            for id in FiniteKripkeFrame::<4>::all_ids_iter() {
                vec.push(FiniteKripkeFrame::<4>::compute_from_u16_id(id as u16));
            }
            vec
        });

        &CACHE[id as usize]
    }

    pub fn swap_to_cached(&self) -> &'static FiniteKripkeFrame<4> {
        FiniteKripkeFrame::<4>::from_u16_id(self.to_u16_id())
    }

    fn canonicalized_frame_id(id: u16) -> u16 {
        static CACHE: LazyLock<Vec<u16>> = LazyLock::new(|| {
            // initially let all elements look at the empty frame
            let mut vec = vec![];
            vec.resize_with(FiniteKripkeFrame::<4>::ALL_FRAMES_COUNT, || 0u16);

            for i in FiniteKripkeFrame::<4>::all_ids_iter() {
                if i == 0 || vec[i as usize] != 0 {
                    continue;
                }

                // Since we are looking frames in increasing order of IDs,
                // the first time we see a frame in an isomorphism class
                // is the canonicalized one.
                FiniteKripkeFrame::<4>::from_u16_id(i)
                    .isomorphism_classes_with_possible_duplications()
                    .for_each(|frame| {
                        vec[frame.to_u16_id() as usize] = i;
                    });
            }
            vec
        });

        CACHE[id as usize]
    }

    pub fn canonicalize(&self) -> &'static FiniteKripkeFrame<4> {
        FiniteKripkeFrame::<4>::from_u16_id(Self::canonicalized_frame_id(self.to_u16_id()))
    }

    fn frame_at_id_is_canonical(id: u16) -> bool {
        static FLAGS: LazyLock<Vec<bool>> = LazyLock::new(|| {
            let mut vec = Vec::with_capacity(FiniteKripkeFrame::<4>::ALL_FRAMES_COUNT);
            for i in FiniteKripkeFrame::<4>::all_ids_iter() {
                vec.push(FiniteKripkeFrame::<4>::canonicalized_frame_id(i) == i);
            }
            vec
        });

        FLAGS[id as usize]
    }

    fn canonical_frames_ids() -> &'static [u16] {
        static FRAMES: LazyLock<Vec<u16>> = LazyLock::new(|| {
            let mut vec = Vec::with_capacity(FiniteKripkeFrame::<4>::NO_OF_FRAMES_UPTO_ISOMORPHISM);
            for id in FiniteKripkeFrame::<4>::all_ids_iter() {
                if FiniteKripkeFrame::<4>::frame_at_id_is_canonical(id) {
                    vec.push(id);
                }
            }
            vec
        });

        &FRAMES
    }

    pub fn canonical_frames() -> &'static [&'static FiniteKripkeFrame<4>] {
        static FRAMES: LazyLock<Vec<&'static FiniteKripkeFrame<4>>> = LazyLock::new(|| {
            let ids = FiniteKripkeFrame::<4>::canonical_frames_ids();
            let mut vec = Vec::with_capacity(ids.len());
            for &id in ids.iter() {
                vec.push(FiniteKripkeFrame::<4>::from_u16_id(id));
            }
            vec
        });

        &FRAMES
    }

    pub fn canonical_frames_grouped_by_accessibility_count()
    -> &'static BTreeMap<u8, Vec<&'static FiniteKripkeFrame<4>>> {
        static GROUPED: LazyLock<BTreeMap<u8, Vec<&'static FiniteKripkeFrame<4>>>> =
            LazyLock::new(|| {
                let mut map = BTreeMap::new();
                for frame in FiniteKripkeFrame::<4>::canonical_frames() {
                    let count = frame.accessibility_relation_count() as u8;
                    map.entry(count).or_insert_with(Vec::new).push(*frame);
                }
                map
            });

        &GROUPED
    }
}

#[cfg(test)]
mod tests {
    use super::FiniteKripkeFrame;

    #[test]
    fn to_from_u16_id() {
        for id in 0u16..=0xFFFF {
            let frame = FiniteKripkeFrame::from_u16_id(id);
            let id_back = frame.to_u16_id();
            assert_eq!(id, id_back);
        }
    }

    #[test]
    fn canonical_frames_count_eq_no_of_frames_upto_iso() {
        assert_eq!(
            FiniteKripkeFrame::<4>::canonical_frames().len(),
            FiniteKripkeFrame::<4>::NO_OF_FRAMES_UPTO_ISOMORPHISM
        );
    }
}
