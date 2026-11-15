;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strnlen_Why3_ide_VCstrnlen_count_len_post_goal10:
;; the strnlen count-length postcondition equating the current offset plus
;; the uint64-converted offset distance with the count-adjusted offset, under
;; the stated memory, bounded-string, address-order, and universal nonzero-byte
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snclp10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snclp10-address-base (address)
  (car address))

(defun snclp10-address-offset (address)
  (cdr address))

(defun snclp10-shift (address amount)
  (cons
   (snclp10-address-base address)
   (+ (snclp10-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub snclp10-character-memory (address) t)
(defstub snclp10-allocation (index) t)
(defstub snclp10-region (base) t)
(defstub snclp10-addr-le-op (left right) t)
(defstub snclp10-l-strnlen (address count) t)
(defstub snclp10-to-uint64 (value) t)
(defstub snclp10-linked-op () t)
(defstub snclp10-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snclp10-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (snclp10-address-p address)
      (and
       (integerp
        (snclp10-character-memory address))
       (implies
        (integerp count)
        (integerp
         (snclp10-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (snclp10-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snclp10-region base)))
     (implies
      (integerp value)
      (integerp
       (snclp10-to-uint64 value))))))

(defun snclp10-addr-le-p (left right)
  (if (snclp10-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk snclp10-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (snclp10-address-p left)
      (snclp10-address-p right)
      (equal
       (snclp10-address-base left)
       (snclp10-address-base right)))
     (equal
      (snclp10-addr-le-p left right)
      (<=
       (snclp10-address-offset left)
       (snclp10-address-offset right))))))

(defun snclp10-linked-p ()
  (if (snclp10-linked-op) t nil))

(defun snclp10-sconst-p ()
  (if (snclp10-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snclp10-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snclp10-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk snclp10-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snclp10-is-uint64-p
       (snclp10-to-uint64 value))
      (implies
       (snclp10-is-uint64-p value)
       (equal
        (snclp10-to-uint64 value)
        value))
      (equal
       (snclp10-to-uint64
        (snclp10-to-uint64 value))
       (snclp10-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snclp10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snclp10-address-base address))
    (<= 0
        (snclp10-address-offset address))
    (<=
     (+ (snclp10-address-offset address)
        length)
     (snclp10-allocation
      (snclp10-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved.

(defun-sk snclp10-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snclp10-character-memory
       (snclp10-shift address index))
      0)
     (< index count)
     (snclp10-is-uint64-p index)
     (snclp10-valid-rw-p
      (snclp10-shift address 0)
      (+ 1 index)))))

(defun-sk snclp10-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snclp10-is-sint8-p
       (snclp10-character-memory
        (snclp10-shift address position)))))))

(defun snclp10-valid-bounded-string-p
    (address count)
  (or
   (snclp10-valid-rw-p
    (snclp10-shift address 0)
    (+ 1 count))
   (and
    (snclp10-bounded-zero-witness-p
     address count)
    (snclp10-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk snclp10-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snclp10-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snclp10-character-memory
             (snclp10-shift address 0))
            0))
          (equal
           (snclp10-l-strnlen address count)
           0)
        (equal
         (snclp10-to-uint64
          (+ 1
             (snclp10-l-strnlen
              (snclp10-shift address 1)
              (snclp10-to-uint64
               (- count 1)))))
         (snclp10-l-strnlen address count)))
      (snclp10-is-uint64-p
       (snclp10-l-strnlen address count))))))

;; The two source nonzero-byte hypotheses retain their universal quantifiers
;; over all mathematical integers.

(defun-sk snclp10-nonzero-before-offset-p
    (address start-offset end-offset)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< (+ position start-offset)
          end-offset)
       (not
        (equal
         (snclp10-character-memory
          (snclp10-shift address position))
         0)))))))

(defun-sk snclp10-nonzero-through-count-p
    (address start-offset count-adjusted-offset)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (<= (+ position start-offset)
           count-adjusted-offset)
       (not
        (equal
         (snclp10-character-memory
          (snclp10-shift address position))
         0)))))))

(defun-sk
    ntp4vc-strnlen-count-len-post-goal10-statement ()
  (forall
   (a1 a i)
   (implies
    (and
     (snclp10-address-p a1)
     (snclp10-address-p a)
     (integerp i)
     (snclp10-function-types-p)
     (snclp10-address-order-law-p)
     (snclp10-to-uint64-laws-p)
     (snclp10-strnlen-laws-p))
    (let*
        ((x
          (snclp10-address-offset a1))
         (x1
          (snclp10-address-offset a))
         (x3
          (- (+ i x1) x))
         (x4
          (snclp10-l-strnlen a1 x3))
         (x5
          (+ i x1)))
      (implies
       (and
        (not (equal i 0))
        (equal
         (snclp10-character-memory a)
         0)
        (equal
         (+ x x4)
         (+ x1
            (snclp10-l-strnlen a i)))
        (<= 0 i)
        (<= x x1)
        (<=
         (snclp10-region
          (snclp10-address-base a1))
         0)
        (snclp10-linked-p)
        (snclp10-sconst-p)
        (snclp10-is-uint64-p i)
        (snclp10-addr-le-p a1 a)
        (snclp10-valid-bounded-string-p
         a i)
        (snclp10-is-uint64-p x3)
        (snclp10-valid-bounded-string-p
         a1 x3)
        (snclp10-addr-le-p
         a
         (snclp10-shift a1 x4))
        (snclp10-nonzero-before-offset-p
         a1 x x1)
        (snclp10-nonzero-through-count-p
         a1 x x5))
       (equal
        (+ x
           (snclp10-to-uint64
            (- x1 x)))
        x5))))))

(value-triple :itpeval-statement-checked)

:q
