extern crate sparse_table;

use sparse_table::SparseTable;
use std::cmp::min;

pub struct SuffixArray {
    s: Vec<u8>,
    order: Vec<usize>,
    index: Vec<usize>,
    lcp: SparseTable<usize>
}

impl SuffixArray {
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

    fn calculate_lcp(s: &[u8], order: &[usize], index: &[usize]) -> Vec<usize> {
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

    pub fn new(s: &[u8]) -> Self {
        let mut order: Vec<usize> = (0..s.len() + 1).collect();
        let mut index: Vec<usize> = s.iter().map(|x| *x as usize).collect();
        index.push(0);

        let mut prev_index = index.clone();
        Self::sort_suffixes(&mut order, &mut index, |i: &usize| prev_index[*i]);

        let mut size = 1;
        while size <= s.len() {
            prev_index.copy_from_slice(&index);
            Self::sort_suffixes(&mut order, &mut index, |i: &usize| {
                (prev_index[*i], prev_index[(*i + size) % prev_index.len()])
            });
            size *= 2;
        }

        let lcp = SparseTable::from(Self::calculate_lcp(s, &order, &index));

        SuffixArray {
            s: s.to_vec(),
            order: order,
            index: index,
            lcp: lcp
        }
    }

    fn lcp(s1: &[u8], s2: &[u8]) -> usize {
        for (pos, (l, r)) in s1.iter().zip(s2.iter()).enumerate() {
            if l != r {
                return pos;
            }
        }
        min(s1.len(), s2.len())
    }

    fn lower_bound(&self, t: &[u8]) -> (usize, usize) {
        let mut l = 0;
        let mut l_lcp = Self::lcp(&self.s[self.order[l]..], t);

        if l_lcp == t.len() || (self.s.len() > self.order[l] + l_lcp &&
                                t[l_lcp] < self.s[self.order[l] + l_lcp]) {
            return (self.order[l], l_lcp);
        }

        let mut r = self.order.len() - 1;
        let mut r_lcp = Self::lcp(&self.s[self.order[r]..], t);

        if r_lcp < t.len() && (self.s.len() <= self.order[r] + r_lcp ||
                               t[r_lcp] > self.s[self.order[r] + r_lcp]) {
            return (r + 1, 0);
        }

        while r - l > 1 {
            let m = l + (r - l) / 2;
            let m_lcp = if l_lcp > r_lcp {
                let lcp = *self.lcp.smallest(l + 1, m + 1);
                if lcp >= l_lcp {
                    l_lcp + Self::lcp(&self.s[self.order[m] + l_lcp..],
                                      &t[l_lcp..])
                } else {
                    lcp
                }
            } else {
                let lcp = *self.lcp.smallest(m + 1, r + 1);
                if lcp >= r_lcp {
                    r_lcp + Self::lcp(&self.s[self.order[m] + r_lcp..],
                                      &t[r_lcp..])
                } else {
                    lcp
                }
            };
            if m_lcp == t.len() || (self.s.len() > self.order[m] + m_lcp &&
                                    t[m_lcp] < self.s[self.order[m] + m_lcp]) {
                r = m;
                r_lcp = m_lcp;
            } else {
                l = m;
                l_lcp = m_lcp;
            }
        }
        (r, r_lcp)
    }

    pub fn find(&self, t: &[u8]) -> Option<usize> {
        let (index, lcp) = self.lower_bound(t);
        if lcp == t.len() {
            return Some(self.order[index]);
        }
        None
    }
}


#[test]
fn test_suffix_array_new() {
    let test1 = "aaa".as_bytes();
    let sa1 = SuffixArray::new(test1);
    assert_eq!(sa1.s, test1);
    assert_eq!(sa1.order, vec![3, 2, 1, 0]);
    assert_eq!(sa1.index, vec![3, 2, 1, 0]);

    let test2 = "".as_bytes();
    let sa2 = SuffixArray::new(test2);
    assert_eq!(sa2.s, test2);
    assert_eq!(sa2.order, vec![0]);
    assert_eq!(sa2.index, vec![0]);

    let test3 = "abc".as_bytes();
    let sa3 = SuffixArray::new(test3);
    assert_eq!(sa3.s, test3);
    assert_eq!(sa3.order, vec![3, 0, 1, 2]);
    assert_eq!(sa3.index, vec![1, 2, 3, 0]);

    let test4 = "ababababa".as_bytes();
    let sa4 = SuffixArray::new(test4);
    assert_eq!(sa4.s, test4);
    assert_eq!(sa4.order, vec![9, 8, 6, 4, 2, 0, 7, 5, 3, 1]);
    assert_eq!(sa4.index, vec![5, 9, 4, 8, 3, 7, 2, 6, 1, 0]);
}

#[test]
fn test_suffix_array_calculate_lcp() {
     let test1 = "aaa".as_bytes();
     let sa1 = SuffixArray::new(test1);
     assert_eq!(SuffixArray::calculate_lcp(&sa1.s, &sa1.order, &sa1.index),
                vec![0, 0, 1, 2]);

     let test2 = "".as_bytes();
     let sa2 = SuffixArray::new(test2);
     assert_eq!(SuffixArray::calculate_lcp(&sa2.s, &sa2.order, &sa2.index),
                vec![0]);

     let test3 = "abc".as_bytes();
     let sa3 = SuffixArray::new(test3);
     assert_eq!(SuffixArray::calculate_lcp(&sa3.s, &sa3.order, &sa3.index),
                vec![0, 0, 0, 0]);

     let test4 = "ababababa".as_bytes();
     let sa4 = SuffixArray::new(test4);
     assert_eq!(SuffixArray::calculate_lcp(&sa4.s, &sa4.order, &sa4.index),
                vec![0, 0, 1, 3, 5, 7, 0, 2, 4, 6]);
}

#[test]
fn test_suffix_array_find() {
     let sa1 = SuffixArray::new("aaa".as_bytes());
     match sa1.find("".as_bytes()) {
          Some(index) => assert!(index <= "aaa".len()),
          _ => assert!(false)
     }
     match sa1.find("a".as_bytes()) {
          Some(index) => assert!("aaa"[index..].starts_with("a")),
          _ => assert!(false),
     }
     match sa1.find("aa".as_bytes()) {
          Some(index) => assert!("aaa"[index..].starts_with("aa")),
          _ => assert!(false)
     }
     match sa1.find("aaa".as_bytes()) {
          Some(index) => assert!("aaa"[index..].starts_with("aaa")),
          _ => assert!(false)
     }
     match sa1.find("aaaa".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }
     match sa1.find("b".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }
     match sa1.find("ab".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }
     match sa1.find("aab".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }
     match sa1.find("aaab".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }

     let sa2 = SuffixArray::new("ababababa".as_bytes());
     match sa2.find("a".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("a")),
          _ => assert!(false)
     }
     match sa2.find("b".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("b")),
          _ => assert!(false)
     }
     match sa2.find("ab".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("ab")),
          _ => assert!(false)
     }
     match sa2.find("ba".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("ba")),
          _ => assert!(false)
     }
     match sa2.find("aba".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("aba")),
          _ => assert!(false)
     }
     match sa2.find("bab".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("bab")),
          _ => assert!(false)
     }
     match sa2.find("abab".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("abab")),
          _ => assert!(false)
     }
     match sa2.find("baba".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("baba")),
          _ => assert!(false)
     }
     match sa2.find("ababa".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("ababa")),
          _ => assert!(false)
     }
     match sa2.find("babab".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("babab")),
          _ => assert!(false)
     }
     match sa2.find("ababab".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("ababab")),
          _ => assert!(false)
     }
     match sa2.find("bababa".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("bababa")),
          _ => assert!(false)
     }
     match sa2.find("abababa".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("abababa")),
          _ => assert!(false)
     }
     match sa2.find("bababab".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("bababab")),
          _ => assert!(false)
     }
     match sa2.find("abababab".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("abababab")),
          _ => assert!(false)
     }
     match sa2.find("babababa".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("babababa")),
          _ => assert!(false)
     }
     match sa2.find("ababababa".as_bytes()) {
          Some(index) => assert!("ababababa"[index..].starts_with("ababababa")),
          _ => assert!(false)
     }
     match sa2.find("babababab".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }
     match sa2.find("aa".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }
     match sa2.find("bb".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }
     match sa2.find("ac".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }
     match sa2.find("bc".as_bytes()) {
          None => assert!(true),
          _ => assert!(false)
     }
}
