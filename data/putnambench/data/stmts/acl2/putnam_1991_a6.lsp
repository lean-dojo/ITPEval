;; Statement-only formalization of PutnamBench corpus artifact putnam_1991_a6:
;; two classes of positive-integer compositions of every n >= 1, one defined
;; by strict two-step inequalities and the other by a recurrence sequence with
;; prefix coverage, have equal cardinalities. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A mask below 2^(n-1) records the separator choices between n unit symbols.
;; This is a bijection with the nonempty finite sequences of positive integers
;; having sum n, hence with the finite positive prefixes of the source
;; eventually-zero functions.
(defun putnam-1991-a6-mask-to-composition-aux
    (units mask current-part reversed-parts)
  (declare (xargs :measure (nfix units)))
  (if (zp units)
      (reverse reversed-parts)
    (if (equal units 1)
        (reverse (cons current-part reversed-parts))
      (if (equal (mod mask 2) 1)
          (putnam-1991-a6-mask-to-composition-aux
           (- units 1)
           (floor mask 2)
           1
           (cons current-part reversed-parts))
        (putnam-1991-a6-mask-to-composition-aux
         (- units 1)
         (floor mask 2)
         (+ current-part 1)
         reversed-parts)))))

(defun putnam-1991-a6-mask-to-composition (n mask)
  (if (and (posp n)
           (natp mask)
           (< mask (expt 2 (- n 1))))
      (putnam-1991-a6-mask-to-composition-aux
       n mask 1 nil)
    nil))

;; This is exactly a_i > a_(i+1)+a_(i+2) at every available triple,
;; together with the final condition a_(r-1) > a_r.
(defun putnam-1991-a6-a-valid-p (composition)
  (cond
   ((endp composition) nil)
   ((endp (cdr composition)) t)
   ((endp (cddr composition))
    (> (car composition) (cadr composition)))
   (t
    (and
     (> (car composition)
        (+ (cadr composition) (caddr composition)))
     (putnam-1991-a6-a-valid-p (cdr composition))))))

(defun putnam-1991-a6-g (index)
  (declare (xargs :measure (nfix index)))
  (cond
   ((zp index) 1)
   ((equal index 1) 2)
   (t
    (+ (putnam-1991-a6-g (- index 1))
       (putnam-1991-a6-g (- index 2))
       1))))

;; Since g_j >= j+1, searching indices from VALUE down to zero is unbounded
;; in the source parameter yet contains every possible witness to g_j=VALUE.
(defun putnam-1991-a6-g-value-p (value index)
  (declare (xargs :measure (nfix index)))
  (if (equal value (putnam-1991-a6-g index))
      t
    (if (zp index)
        nil
      (putnam-1991-a6-g-value-p value (- index 1)))))

(defun putnam-1991-a6-all-g-values-p (composition)
  (if (consp composition)
      (and
       (putnam-1991-a6-g-value-p
        (car composition) (car composition))
       (putnam-1991-a6-all-g-values-p (cdr composition)))
    (equal composition nil)))

(defun putnam-1991-a6-nonincreasing-p (composition)
  (if (and (consp composition)
           (consp (cdr composition)))
      (and
       (>= (car composition) (cadr composition))
       (putnam-1991-a6-nonincreasing-p (cdr composition)))
    t))

(defun putnam-1991-a6-member-p (value composition)
  (if (consp composition)
      (or (equal value (car composition))
          (putnam-1991-a6-member-p value (cdr composition)))
    nil))

(defun putnam-1991-a6-g-prefix-covered-p (composition index)
  (declare (xargs :measure (nfix index)))
  (and
   (putnam-1991-a6-member-p
    (putnam-1991-a6-g index) composition)
   (if (zp index)
       t
     (putnam-1991-a6-g-prefix-covered-p
      composition (- index 1)))))

;; This bounded search is exactly the source existential k: if the first part
;; is g_k, then k is below that positive first part because g_k >= k+1.
(defun putnam-1991-a6-leading-prefix-p
    (composition index)
  (declare (xargs :measure (nfix index)))
  (if (equal (car composition)
             (putnam-1991-a6-g index))
      (putnam-1991-a6-g-prefix-covered-p composition index)
    (if (zp index)
        nil
      (putnam-1991-a6-leading-prefix-p
       composition (- index 1)))))

(defun putnam-1991-a6-b-valid-p (composition)
  (and
   (consp composition)
   (putnam-1991-a6-nonincreasing-p composition)
   (putnam-1991-a6-all-g-values-p composition)
   (putnam-1991-a6-leading-prefix-p
    composition (car composition))))

(defun putnam-1991-a6-count-a-codes
    (n remaining-codes)
  (declare (xargs :measure (nfix remaining-codes)))
  (if (zp remaining-codes)
      0
    (let* ((code (- remaining-codes 1))
           (composition
            (putnam-1991-a6-mask-to-composition n code)))
      (+
       (if (putnam-1991-a6-a-valid-p composition) 1 0)
       (putnam-1991-a6-count-a-codes n code)))))

(defun putnam-1991-a6-count-b-codes
    (n remaining-codes)
  (declare (xargs :measure (nfix remaining-codes)))
  (if (zp remaining-codes)
      0
    (let* ((code (- remaining-codes 1))
           (composition
            (putnam-1991-a6-mask-to-composition n code)))
      (+
       (if (putnam-1991-a6-b-valid-p composition) 1 0)
       (putnam-1991-a6-count-b-codes n code)))))

(defun putnambench-putnam-1991-a6-statement (n)
  (implies
   (and (natp n)
        (<= 1 n))
   (equal
    (putnam-1991-a6-count-a-codes
     n (expt 2 (- n 1)))
    (putnam-1991-a6-count-b-codes
     n (expt 2 (- n 1))))))

(value-triple :itpeval-statement-checked)
:q
