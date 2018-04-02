fn build_lcp(s: &[u8], order: &[usize], index: &[usize]) -> Vec<usize> {
    let mut lcp = vec![0; order.len()];
    let mut plen = 0;
    for curr in 0..s.len() {
        let prev = order[index[curr] - 1];
        while curr + plen < s.len() && prev + plen < s.len() &&
              s[curr + plen] == s[prev + plen] {
            plen += 1;
        }
        lcp[index[curr]] = plen;
        if plen > 0 {
            plen -= 1;
        }
    }
    lcp
}

fn sort_suffixes<K, F>(order: &mut [usize], index: &mut [usize], get_key: F)
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

pub struct SuffixArray {
    s: Vec<u8>,
    order: Vec<usize>,
    index: Vec<usize>,
    lcp: Vec<usize>
}

impl SuffixArray {
    pub fn new(s: &[u8]) -> SuffixArray {
        let mut order: Vec<usize> = (0..s.len() + 1).collect();
        let mut index: Vec<usize> = s.iter().map(|x| *x as usize).collect();
        index.push(0);

        let mut prev_index = index.clone();
        sort_suffixes(&mut order, &mut index, |i: &usize| prev_index[*i]);

        let mut size = 1;
        while size <= s.len() {
            prev_index.copy_from_slice(&index);
            sort_suffixes(&mut order, &mut index, |i: &usize| {
                (prev_index[*i], prev_index[(*i + size) % prev_index.len()])
            });
            size *= 2;
        }

        SuffixArray {
            s: s.to_vec(),
            lcp: build_lcp(s, &order, &index),
            order: order,
            index: index
        }
    }
}


#[test]
fn suffix_array_new_test() {
    let test1 = "aaa".as_bytes();
    let sa1 = SuffixArray::new(test1);
    assert_eq!(sa1.s, test1);
    assert_eq!(sa1.order, vec![3, 2, 1, 0]);
    assert_eq!(sa1.index, vec![3, 2, 1, 0]);
    assert_eq!(sa1.lcp, vec![0, 0, 1, 2]);

    let test2 = "".as_bytes();
    let sa2 = SuffixArray::new(test2);
    assert_eq!(sa2.s, test2);
    assert_eq!(sa2.order, vec![0]);
    assert_eq!(sa2.index, vec![0]);
    assert_eq!(sa2.lcp, vec![0]);

    let test3 = "abc".as_bytes();
    let sa3 = SuffixArray::new(test3);
    assert_eq!(sa3.s, test3);
    assert_eq!(sa3.order, vec![3, 0, 1, 2]);
    assert_eq!(sa3.index, vec![1, 2, 3, 0]);
    assert_eq!(sa3.lcp, vec![0, 0, 0, 0]);

    let test4 = "ababababa".as_bytes();
    let sa4 = SuffixArray::new(test4);
    assert_eq!(sa4.s, test4);
    assert_eq!(sa4.order, vec![9, 8, 6, 4, 2, 0, 7, 5, 3, 1]);
    assert_eq!(sa4.index, vec![5, 9, 4, 8, 3, 7, 2, 6, 1, 0]);
    assert_eq!(sa4.lcp, vec![0, 0, 1, 3, 5, 7, 0, 2, 4, 6]);
}
