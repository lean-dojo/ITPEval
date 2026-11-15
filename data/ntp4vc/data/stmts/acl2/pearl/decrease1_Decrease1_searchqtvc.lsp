;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/decrease1_Decrease1_searchqtvc: the iterative-search verification
;; condition for an integer list whose adjacent values decrease by at most one,
;; including loop progress and first-zero result specifications. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite proper lists of integers directly represent the
;; source integers and List Z values. The accessor implements Int.toNat and
;; the source integer-list default value zero.

(defun ntp4vc-decrease1-search-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-decrease1-search-integer-list-p (cdr xs)))))

(defun ntp4vc-decrease1-search-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-decrease1-search-nth-int (index xs)
  (let ((value
         (nth
          (ntp4vc-decrease1-search-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; This is the source decrease1 predicate, retaining its universal
;; quantification over every mathematical integer index.

(defun-sk ntp4vc-decrease1-search-decrease1-p (a)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (- (len a) 1)))
      (<=
       (- (ntp4vc-decrease1-search-nth-int index a) 1)
       (ntp4vc-decrease1-search-nth-int (+ index 1) a))))))

;; The source uses both plain half-open zero-free ranges and ranges whose
;; conclusion is additionally guarded by the list length.

(defun-sk ntp4vc-decrease1-search-zero-free-range-p (a upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (not
       (equal
        (ntp4vc-decrease1-search-nth-int index a)
        0))))))

(defun-sk ntp4vc-decrease1-search-zero-free-guarded-p (a upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index upper))
      (implies
       (< index (len a))
       (not
        (equal
         (ntp4vc-decrease1-search-nth-int index a)
         0)))))))

;; This is the exact conditional conclusion for one loop index I, including
;; the repeated bounds and both explicit termination-measure inequalities.

(defun ntp4vc-decrease1-search-index-conclusion-p (a i)
  (if (< i (len a))
      (and
       (<= 0 i)
       (< i (len a))
       (if
           (equal
            (ntp4vc-decrease1-search-nth-int i a)
            0)
           (or
            (and
             (equal i -1)
             (ntp4vc-decrease1-search-zero-free-range-p
              a (len a)))
            (and
             (<= 0 i)
             (< i (len a))
             (equal
              (ntp4vc-decrease1-search-nth-int i a)
              0)
             (ntp4vc-decrease1-search-zero-free-range-p
              a i)))
         (and
          (<= 0 i)
          (< i (len a))
          (if
              (<
               0
               (ntp4vc-decrease1-search-nth-int i a))
              (and
               (<= 0 i)
               (< i (len a))
               (<= 0 (- (len a) i))
               (<
                (-
                 (len a)
                 (+
                  i
                  (ntp4vc-decrease1-search-nth-int i a)))
                (- (len a) i))
               (<=
                0
                (+
                 i
                 (ntp4vc-decrease1-search-nth-int i a)))
               (ntp4vc-decrease1-search-zero-free-guarded-p
                a
                (+
                 i
                 (ntp4vc-decrease1-search-nth-int i a))))
            (and
             (<= 0 (- (len a) i))
             (<
              (- (len a) (+ i 1))
              (- (len a) i))
             (<= 0 (+ i 1))
             (ntp4vc-decrease1-search-zero-free-guarded-p
              a (+ i 1)))))))
    (or
     (ntp4vc-decrease1-search-zero-free-range-p a (len a))
     (and
      (<= 0 -1)
      (< -1 (len a))
      (equal
       (ntp4vc-decrease1-search-nth-int -1 a)
       0)
      (ntp4vc-decrease1-search-zero-free-range-p a -1)))))

;; I remains universally quantified over all mathematical integers, and its
;; loop-invariant premise remains inside that quantifier.

(defun-sk ntp4vc-decrease1-search-all-indices-p (a)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (ntp4vc-decrease1-search-zero-free-guarded-p a i))
      (ntp4vc-decrease1-search-index-conclusion-p a i)))))

(defun
  ntp4vc-pearl-decrease1-decrease1-searchqtvc-statement
  (a)
  (implies
   (and
    (ntp4vc-decrease1-search-integer-list-p a)
    (ntp4vc-decrease1-search-decrease1-p a))
   (and
    (<= 0 0)
    (ntp4vc-decrease1-search-zero-free-guarded-p a 0)
    (ntp4vc-decrease1-search-all-indices-p a))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
