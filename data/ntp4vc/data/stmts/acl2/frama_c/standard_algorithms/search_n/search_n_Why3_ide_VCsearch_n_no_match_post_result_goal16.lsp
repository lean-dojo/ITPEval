;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_no_match_post_result_goal16:
;; the search_n no-match branch returns the recorded end index under the
;; stated integer bounds, constant-range exclusions, linkedness, and
;; memory-readability hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sn16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sn16-address-base (address)
  (car address))

(defun sn16-address-offset (address)
  (cdr address))

(defun sn16-shift (address amount)
  (cons
   (sn16-address-base address)
   (+ (sn16-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub sn16-integer-memory (address) t)
(defstub sn16-allocation (index) t)
(defstub sn16-region (base) t)
(defstub sn16-linked-op () t)

(defun-sk sn16-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (sn16-address-p address)
      (integerp (sn16-integer-memory address)))
     (implies
      (integerp index)
      (integerp (sn16-allocation index)))
     (implies
      (integerp base)
      (integerp (sn16-region base))))))

(defun sn16-linked-p ()
  (if (sn16-linked-op) t nil))

(defun sn16-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun sn16-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun sn16-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun sn16-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (sn16-address-base address)))
    (<= 0 (sn16-address-offset address))
    (<=
     (+ (sn16-address-offset address) length)
     (sn16-allocation (sn16-address-base address))))))

;; Exact unfolding of Axiomatic.p_constantrange over every mathematical
;; integer index.

(defun-sk sn16-constant-range-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (sn16-integer-memory (sn16-shift a index))
      value))))

;; Exact unfolding of Axiomatic.p_hasconstantsubrange. The existential witness
;; remains internal to this predicate.

(defun-sk sn16-has-constant-subrange-p (a maximum length value)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (<= (+ length index) maximum)
     (sn16-constant-range-p
      a index (+ length index) value))))

(defun-sk ntp4vc-search-n-no-match-post-result-goal16-statement ()
  (forall
   (a i i7 i3 i1 i2 i4 i5 i6 i8)
   (implies
    (and
     (sn16-address-p a)
     (integerp i)
     (integerp i7)
     (integerp i3)
     (integerp i1)
     (integerp i2)
     (integerp i4)
     (integerp i5)
     (integerp i6)
     (integerp i8)
     (sn16-function-types-p))
    (let*
        ((x
          (sn16-integer-memory
           (sn16-shift a (- i 1))))
         (x1 (+ 1 i7))
         (a1 (sn16-shift a i7))
         (x2 (+ i3 (sn16-to-uint32 x1))))
      (implies
       (and
        (<= (sn16-region (sn16-address-base a)) 0)
        (sn16-linked-p)
        (sn16-is-uint32-p i)
        (sn16-is-uint32-p i1)
        (sn16-is-uint32-p i2)
        (sn16-is-uint32-p i3)
        (sn16-is-uint32-p i4)
        (sn16-is-uint32-p i5)
        (sn16-is-uint32-p i6)
        (sn16-is-uint32-p i7)
        (sn16-is-sint32-p i8)
        (not
         (sn16-has-constant-subrange-p
          a i5 i3 i8))
        (sn16-valid-rd-p (sn16-shift a 0) i5)
        (sn16-is-sint32-p x)
        (if
            (< 0 i3)
            (if
                (<= i3 i5)
                (and
                 (equal i5 i4)
                 (equal i6 i4)
                 (equal i6 i5)
                 (<= i x1)
                 (sn16-constant-range-p a i i7 i8)
                 (not
                  (sn16-has-constant-subrange-p
                   a i7 i3 i8))
                 (if
                     (< i7 i5)
                     (and
                      (equal (+ i i3) x1)
                      (equal (+ i1 i3) x1)
                      (equal (+ i2 i3) x1)
                      (equal (sn16-integer-memory a1) i8)
                      (< i7 x2)
                      (<= i7 4294967294)
                      (<= x2 (+ 4294967296 i7))
                      (sn16-valid-rd-p a1 1))
                   (equal i5 i2))
                 (implies
                  (< 0 i)
                  (not (equal x i8))))
              (equal i5 i2))
          (equal i2 0)))
       (equal i5 i2))))))

(value-triple :itpeval-statement-checked)

:q
