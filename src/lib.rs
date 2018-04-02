pub struct SuffixArray {
    s: Vec<u8>,
    order: Vec<usize>,
    index: Vec<usize>
}

fn sort_suffix_array<K, F>(order: &mut [usize],
                           index: &mut [usize],
                           get_key: F)
        where F: (Fn(&usize) -> K), K: Ord {
    order.sort_unstable_by_key(&get_key);
    let mut current = 0;
    for i in 1..order.len() {
        if get_key(&order[i]) != get_key(&order[i - 1]) {
            current += 1;
        }
        index[order[i]] = current;
    }
}

pub fn build_suffix_array(s: &[u8]) -> SuffixArray {
    let mut order: Vec<usize> = (0..s.len() + 1).collect();
    let mut index: Vec<usize> = s.iter().map(|x| *x as usize).collect();
    index.push(0);

    let mut prev_index = index.clone();
    sort_suffix_array(&mut order, &mut index, |i: &usize| prev_index[*i]);

    let mut size = 1;
    while size <= s.len() {
        prev_index.copy_from_slice(&index);
        sort_suffix_array(&mut order, &mut index, |i: &usize| {
            (prev_index[*i], prev_index[(*i + size) % prev_index.len()])
        });
        size *= 2;
    }

    SuffixArray {
        s: s.to_vec(),
        order: order,
        index: index
    }
}

#[test]
fn build_suffix_array_test() {
    let test1 = "aaa".as_bytes();
    let sa1 = build_suffix_array(test1);
    assert_eq!(sa1.s, test1);
    assert_eq!(sa1.order, vec![3, 2, 1, 0]);
    assert_eq!(sa1.index, vec![3, 2, 1, 0]);

    let test2 = "".as_bytes();
    let sa2 = build_suffix_array(test2);
    assert_eq!(sa2.s, test2);
    assert_eq!(sa2.order, vec![0]);
    assert_eq!(sa2.index, vec![0]);

    let test3 = "abc".as_bytes();
    let sa3 = build_suffix_array(test3);
    assert_eq!(sa3.s, test3);
    assert_eq!(sa3.order, vec![3, 0, 1, 2]);
    assert_eq!(sa3.index, vec![1, 2, 3, 0]);
}
