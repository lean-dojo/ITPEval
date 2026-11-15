;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__045, "The Partition Theorem (Euler)": for every
;; natural number n, the number of partitions of n into distinct positive
;; parts equals the number of partitions of n into odd positive parts. The
;; recursive counters enumerate these two finite partition classes. This file
;; contains no proof.

(in-package "ACL2")

(defun ht045-count-distinct-partitions-through-part
    (remaining part)
  (declare (xargs :measure (nfix part)))
  (if (and (natp remaining)
           (natp part))
      (if (zp part)
          (if (zp remaining) 1 0)
        (+ (ht045-count-distinct-partitions-through-part
            remaining (- part 1))
           (if (<= part remaining)
               (ht045-count-distinct-partitions-through-part
                (- remaining part) (- part 1))
             0)))
    0))

(defun ht045-count-odd-partitions-through-part
    (remaining part)
  (declare (xargs :measure (+ (nfix remaining) (nfix part))))
  (if (and (natp remaining)
           (natp part))
      (if (zp part)
          (if (zp remaining) 1 0)
        (if (equal (mod part 2) 0)
            (ht045-count-odd-partitions-through-part
             remaining (- part 1))
          (if (<= part remaining)
              (+ (ht045-count-odd-partitions-through-part
                  remaining (- part 1))
                 (ht045-count-odd-partitions-through-part
                  (- remaining part) part))
            (ht045-count-odd-partitions-through-part
             remaining (- part 1)))))
    0))

(defun ht045-distinct-partition-count (n)
  (if (natp n)
      (ht045-count-distinct-partitions-through-part n n)
    0))

(defun ht045-odd-partition-count (n)
  (if (natp n)
      (ht045-count-odd-partitions-through-part n n)
    0))

(defun hundred-theorems-045-euler-partition-statement (n)
  (implies
   (natp n)
   (equal
    (ht045-distinct-partition-count n)
    (ht045-odd-partition-count n))))

(value-triple :itpeval-statement-checked)
:q
