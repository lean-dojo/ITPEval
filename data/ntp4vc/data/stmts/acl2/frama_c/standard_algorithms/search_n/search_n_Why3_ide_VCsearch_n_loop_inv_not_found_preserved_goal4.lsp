;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_loop_inv_not_found_preserved_goal4:
;; preservation of the absence of a constant integer-memory subrange after
;; advancing the search_n loop index, under the stated integer bounds,
;; constant-range, linkedness, and memory-readability hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sn4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sn4-address-base (address)
  (car address))

(defun sn4-address-offset (address)
  (cdr address))

(defun sn4-shift (address amount)
  (cons
   (sn4-address-base address)
   (+ (sn4-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub sn4-integer-memory (address) t)
(defstub sn4-allocation (index) t)
(defstub sn4-region (base) t)
(defstub sn4-linked-op () t)

(defun-sk sn4-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (sn4-address-p address)
      (integerp (sn4-integer-memory address)))
     (implies
      (integerp index)
      (integerp (sn4-allocation index)))
     (implies
      (integerp base)
      (integerp (sn4-region base))))))

(defun sn4-linked-p ()
  (if (sn4-linked-op) t nil))

(defun sn4-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun sn4-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun sn4-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (sn4-address-base address)))
    (<= 0 (sn4-address-offset address))
    (<=
     (+ (sn4-address-offset address) length)
     (sn4-allocation (sn4-address-base address))))))

;; Exact unfolding of Axiomatic.p_constantrange over every mathematical
;; integer index.

(defun-sk sn4-constant-range-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (sn4-integer-memory (sn4-shift a index))
      value))))

;; Exact unfolding of Axiomatic.p_hasconstantsubrange. The existential witness
;; remains internal to this predicate.

(defun-sk sn4-has-constant-subrange-p (a maximum length value)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (<= (+ length index) maximum)
     (sn4-constant-range-p
      a index (+ length index) value))))

(defun-sk
    ntp4vc-search-n-loop-inv-not-found-preserved-goal4-statement ()
  (forall
   (i4 a i i2 i3 i1 i5)
   (implies
    (and
     (integerp i4)
     (sn4-address-p a)
     (integerp i)
     (integerp i2)
     (integerp i3)
     (integerp i1)
     (integerp i5)
     (sn4-function-types-p))
    (let*
        ((x (+ 1 i4))
         (a1 (sn4-shift a i4))
         (x1 (sn4-integer-memory a1))
         (x2
          (sn4-integer-memory
           (sn4-shift a (- i 1)))))
      (implies
       (and
        (< 0 i2)
        (<= i2 i3)
        (< i4 i3)
        (<= (sn4-region (sn4-address-base a)) 0)
        (<= i4 4294967294)
        (<= i x)
        (sn4-linked-p)
        (sn4-is-uint32-p i)
        (sn4-is-uint32-p i1)
        (sn4-is-uint32-p i2)
        (sn4-is-uint32-p i3)
        (sn4-is-uint32-p i4)
        (sn4-is-sint32-p i5)
        (sn4-is-uint32-p x)
        (sn4-is-sint32-p x1)
        (sn4-constant-range-p a i i4 i5)
        (not
         (sn4-has-constant-subrange-p
          a i4 i2 i5))
        (sn4-valid-rd-p (sn4-shift a 0) i3)
        (sn4-valid-rd-p a1 1)
        (sn4-is-sint32-p x2)
        (implies
         (< 0 i)
         (not (equal x2 i5))))
       (implies
        (or
         (not (equal x1 i5))
         (and
          (equal i1 i)
          (not (equal (+ i1 i2) x))
          (<= i1 x)
          (<= i4 (+ 4294967294 i1))))
        (not
         (sn4-has-constant-subrange-p
          a x i2 i5))))))))

(value-triple :itpeval-statement-checked)

:q
