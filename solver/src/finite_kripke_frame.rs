use crate::formula::Formula;
use crate::valuation::FiniteValuation;

#[derive(Clone, Copy)]
pub struct FiniteKripkeFrame<const N: usize> {
    accessibility: [[bool; N]; N],
}

#[allow(long_running_const_eval)]
impl FiniteKripkeFrame<4> {
    pub const fn to_u16_id(&self) -> u16 {
        let mut id = 0u16;
        let mut i = 0;
        while i < 4 {
            let mut j = 0;
            while j < 4 {
                if self.accessibility[i][j] {
                    id |= 1 << (i * 4 + j);
                }
                j += 1;
            }
            i += 1;
        }
        id
    }

    pub const fn from_u16_id(id: u16) -> Self {
        let mut accessibility = [[false; 4]; 4];
        let mut i = 0;
        while i < 4 {
            let mut j = 0;
            while j < 4 {
                accessibility[i][j] = (id & (1 << (i * 4 + j))) != 0;
                j += 1;
            }
            i += 1;
        }
        FiniteKripkeFrame { accessibility }
    }

    pub const fn empty_frame() -> Self {
        FiniteKripkeFrame {
            accessibility: [[false; 4]; 4],
        }
    }

    pub const fn canonicalize_to_isomorphic_frame_with_min_id(&self) -> Self {
        let mut min_id = self.to_u16_id();
        let mut best_frame = *self;

        const fn try_perm(
            perm: &mut [usize; 4],
            original: &FiniteKripkeFrame<4>,
            min_id: &mut u16,
            best_frame: &mut FiniteKripkeFrame<4>,
        ) {
            let mut frame = FiniteKripkeFrame::<4>::empty_frame();
            let mut i = 0;
            while i < 4 {
                let mut j = 0;
                while j < 4 {
                    frame.accessibility[i][j] = original.accessibility[perm[i]][perm[j]];
                    j += 1;
                }
                i += 1;
            }
            let id = frame.to_u16_id();
            if id < *min_id {
                *min_id = id;
                *best_frame = frame;
            }
        }

        const fn try_perms(
            items_to_swap: usize,
            current_perm: &mut [usize; 4],
            original: &FiniteKripkeFrame<4>,
            min_id: &mut u16,
            best_frame: &mut FiniteKripkeFrame<4>,
        ) {
            // Heap's algorithm
            if items_to_swap <= 1 {
                try_perm(current_perm, original, min_id, best_frame);
                return;
            }
            let mut i = 0;
            while i < items_to_swap {
                try_perms(
                    items_to_swap - 1,
                    current_perm,
                    original,
                    min_id,
                    best_frame,
                );
                if items_to_swap % 2 == 0 {
                    current_perm.swap(i, items_to_swap - 1);
                } else {
                    current_perm.swap(0, items_to_swap - 1);
                }
                i += 1;
            }
        }

        try_perms(4, &mut [0, 1, 2, 3], self, &mut min_id, &mut best_frame);

        best_frame
    }

    pub const ALL_FRAMES_COUNT: usize = 65536;

    pub const FROM_U16_ID_CACHED: [FiniteKripkeFrame<4>; Self::ALL_FRAMES_COUNT] = {
        let mut frames = [FiniteKripkeFrame::<4>::empty_frame(); Self::ALL_FRAMES_COUNT];
        let mut id = 1u16;
        loop {
            frames[id as usize] = Self::from_u16_id(id);
            if id == 0xFFFF {
                break;
            }
            id += 1;
        }
        frames
    };

    pub const CANONICALIZED_FRAME_ID: [u16; Self::ALL_FRAMES_COUNT] = {
        let mut ids = [0u16; Self::ALL_FRAMES_COUNT];
        let mut i = 0;
        while i < Self::ALL_FRAMES_COUNT {
            ids[i] = Self::FROM_U16_ID_CACHED[i]
                .canonicalize_to_isomorphic_frame_with_min_id()
                .to_u16_id();
            i += 1;
        }
        ids
    };

    pub const FRAME_IS_CANONICALIZED: [bool; Self::ALL_FRAMES_COUNT] = {
        let mut flags = [false; Self::ALL_FRAMES_COUNT];
        let mut i = 0;
        while i < Self::ALL_FRAMES_COUNT {
            flags[i] = Self::CANONICALIZED_FRAME_ID[i] == i as u16;
            i += 1;
        }
        flags
    };

    // https://oeis.org/A000595
    pub const NO_OF_FRAMES_UPTO_ISOMORPHISM: usize = 3044;

    pub const CANONICALIZED_FRAMES_IDS: [u16; Self::NO_OF_FRAMES_UPTO_ISOMORPHISM] = {
        let mut frames = [0u16; Self::NO_OF_FRAMES_UPTO_ISOMORPHISM];
        let mut index = 0;
        let mut id = 0u16;
        while id < Self::ALL_FRAMES_COUNT as u16 {
            if Self::FRAME_IS_CANONICALIZED[id as usize] {
                frames[index] = id;
                index += 1;
            }
            id += 1;
        }
        frames
    };
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

#[cfg(test)]
mod tests {
    #[test]
    fn to_from_u16_id() {
        for id in 0u16..=0xFFFF {
            let frame = super::super::FiniteKripkeFrame::from_u16_id(id);
            let id_back = frame.to_u16_id();
            assert_eq!(id, id_back);
        }
    }

    #[test]
    fn canonicalization_idempotent() {
        for id in 0u16..=0xFFFF {
            let frame = super::super::FiniteKripkeFrame::from_u16_id(id);
            let canonical_frame = frame.canonicalize_to_isomorphic_frame_with_min_id();
            let canonical_frame2 = canonical_frame.canonicalize_to_isomorphic_frame_with_min_id();
            assert_eq!(canonical_frame.to_u16_id(), canonical_frame2.to_u16_id());
        }
    }

    #[test]
    fn canonical_frames_count_eq_no_of_frames_upto_iso() {
        let count = super::super::FiniteKripkeFrame::<4>::CANONICALIZED_FRAME_ID
            .as_slice()
            .iter()
            .enumerate()
            .filter(|a| a.0 == *a.1 as usize)
            .count();
        assert_eq!(
            count,
            super::super::FiniteKripkeFrame::<4>::NO_OF_FRAMES_UPTO_ISOMORPHISM
        );
    }
}
