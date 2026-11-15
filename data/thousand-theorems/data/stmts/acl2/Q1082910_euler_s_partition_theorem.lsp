;; Statement-only formalization of thousand-theorems artifact
;; thousand-theorems__acl2__Q1082910, "Euler's partition theorem": for every
;; natural number n, the number of partitions of n into odd positive parts
;; equals the number of partitions of n into distinct positive parts. The
;; recursive counters enumerate these two finite partition classes. This file
;; contains no proof.

(in-package "ACL2")

(defun q1082910-count-distinct-partitions-through-part
    (remaining part)
  (declare (xargs :measure (nfix part)))
  (if (and (natp remaining)
           (natp part))
      (if (zp part)
          (if (zp remaining) 1 0)
        (+ (q1082910-count-distinct-partitions-through-part
            remaining (- part 1))
           (if (<= part remaining)
               (q1082910-count-distinct-partitions-through-part
                (- remaining part) (- part 1))
             0)))
    0))

(defun q1082910-count-odd-partitions-through-part
    (remaining part)
  (declare (xargs :measure (+ (nfix remaining) (nfix part))))
  (if (and (natp remaining)
           (natp part))
      (if (zp part)
          (if (zp remaining) 1 0)
        (if (equal (mod part 2) 0)
            (q1082910-count-odd-partitions-through-part
             remaining (- part 1))
          (if (<= part remaining)
              (+ (q1082910-count-odd-partitions-through-part
                  remaining (- part 1))
                 (q1082910-count-odd-partitions-through-part
                  (- remaining part) part))
            (q1082910-count-odd-partitions-through-part
             remaining (- part 1)))))
    0))

(defun q1082910-distinct-partition-count (n)
  (if (natp n)
      (q1082910-count-distinct-partitions-through-part n n)
    0))

(defun q1082910-odd-partition-count (n)
  (if (natp n)
      (q1082910-count-odd-partitions-through-part n n)
    0))

(defun thousand-theorems-q1082910-euler-partition-statement (n)
  (implies
   (natp n)
   (equal
    (q1082910-odd-partition-count n)
    (q1082910-distinct-partition-count n))))

(value-triple :itpeval-statement-checked)
:q
