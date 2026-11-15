;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_has_match_post_match_goal14:
;; preservation of a constant integer-memory range after the search_n
;; match branch, under the stated bounds, subrange, linkedness, and
;; memory-readability hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sn14-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sn14-address-base (address)
  (car address))

(defun sn14-address-offset (address)
  (cdr address))

(defun sn14-shift (address amount)
  (cons
   (sn14-address-base address)
   (+ (sn14-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub sn14-integer-memory (address) t)
(defstub sn14-allocation (index) t)
(defstub sn14-region (base) t)
(defstub sn14-linked-op () t)

(defun-sk sn14-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (sn14-address-p address)
      (integerp (sn14-integer-memory address)))
     (implies
      (integerp index)
      (integerp (sn14-allocation index)))
     (implies
      (integerp base)
      (integerp (sn14-region base))))))

(defun sn14-linked-p ()
  (if (sn14-linked-op) t nil))

(defun sn14-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun sn14-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun sn14-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun sn14-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (sn14-address-base address)))
    (<= 0 (sn14-address-offset address))
    (<=
     (+ (sn14-address-offset address) length)
     (sn14-allocation (sn14-address-base address))))))

;; Exact unfolding of Axiomatic.p_constantrange over every mathematical
;; integer index.

(defun-sk sn14-constant-range-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (sn14-integer-memory (sn14-shift a index))
      value))))

;; Exact unfolding of Axiomatic.p_hasconstantsubrange. The existential
;; witness remains internal to this predicate.

(defun-sk sn14-has-constant-subrange-p (a maximum length value)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (<= (+ length index) maximum)
     (sn14-constant-range-p
      a index (+ length index) value))))

(defun-sk ntp4vc-search-n-has-match-post-match-goal14-statement ()
  (forall
   (a i i6 i1 i2 i3 i4 i5 i7)
   (implies
    (and
     (sn14-address-p a)
     (integerp i)
     (integerp i6)
     (integerp i1)
     (integerp i2)
     (integerp i3)
     (integerp i4)
     (integerp i5)
     (integerp i7)
     (sn14-function-types-p))
    (let*
        ((x
          (sn14-integer-memory
           (sn14-shift a (- i 1))))
         (x1 (+ 1 i6))
         (x2 (+ i1 i2))
         (a1 (sn14-shift a i6))
         (x3 (sn14-to-uint32 x1)))
      (implies
       (and
        (<= (sn14-region (sn14-address-base a)) 0)
        (sn14-linked-p)
        (sn14-is-uint32-p i)
        (sn14-is-uint32-p i1)
        (sn14-is-uint32-p i2)
        (sn14-is-uint32-p i3)
        (sn14-is-uint32-p i4)
        (sn14-is-uint32-p i5)
        (sn14-is-uint32-p i6)
        (sn14-is-sint32-p i7)
        (sn14-has-constant-subrange-p a i4 i2 i7)
        (sn14-valid-rd-p (sn14-shift a 0) i4)
        (sn14-is-sint32-p x)
        (if
            (< 0 i2)
            (if
                (<= i2 i4)
                (and
                 (equal i5 i3)
                 (equal i5 i4)
                 (<= i x1)
                 (sn14-constant-range-p a i i6 i7)
                 (not
                  (sn14-has-constant-subrange-p
                   a i6 i2 i7))
                 (if
                     (< i6 i5)
                     (and
                      (equal i1 i)
                      (equal x2 x1)
                      (equal (sn14-integer-memory a1) i7)
                      (<= i1 x3)
                      (<= i6 4294967294)
                      (<= x3 (+ 4294967295 i1))
                      (sn14-valid-rd-p a1 1))
                   (equal i5 i1))
                 (implies
                  (< 0 i)
                  (not (equal x i7))))
              (equal i4 i1))
          (equal i1 0)))
       (sn14-constant-range-p a i1 x2 i7))))))

(value-triple :itpeval-statement-checked)

:q
