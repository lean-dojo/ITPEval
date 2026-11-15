;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strncmp_Why3_ide_VCstrncmp_loop_inv_5_preserved_goal11:
;; preservation of bounded-string validity for both strncmp cursors after
;; advancing each by one, under the stated offset, length, byte,
;; address-order, and pointwise equality hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sng11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sng11-address-base (address)
  (car address))

(defun sng11-address-offset (address)
  (cdr address))

(defun sng11-shift (address amount)
  (cons
   (sng11-address-base address)
   (+ (sng11-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, C integer conversions, linkedness, and
;; constancy symbols.

(defstub sng11-character-memory (address) t)
(defstub sng11-allocation (index) t)
(defstub sng11-region (base) t)
(defstub sng11-addr-le-op (left right) t)
(defstub sng11-l-strnlen (address count) t)
(defstub sng11-to-uint8 (value) t)
(defstub sng11-to-uint64 (value) t)
(defstub sng11-linked-op () t)
(defstub sng11-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sng11-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (sng11-address-p address)
      (and
       (integerp
        (sng11-character-memory address))
       (implies
        (integerp count)
        (integerp
         (sng11-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (sng11-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sng11-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sng11-to-uint8 value))
       (integerp
        (sng11-to-uint64 value)))))))

(defun sng11-addr-le-p (left right)
  (if (sng11-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk sng11-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (sng11-address-p left)
      (sng11-address-p right)
      (equal
       (sng11-address-base left)
       (sng11-address-base right)))
     (equal
      (sng11-addr-le-p left right)
      (<=
       (sng11-address-offset left)
       (sng11-address-offset right))))))

(defun sng11-linked-p ()
  (if (sng11-linked-op) t nil))

(defun sng11-sconst-p ()
  (if (sng11-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sng11-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sng11-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sng11-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source
;; unsigned C integer conversions used by this VC and its strnlen recurrence.

(defun-sk sng11-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng11-is-uint8-p
       (sng11-to-uint8 value))
      (implies
       (sng11-is-uint8-p value)
       (equal
        (sng11-to-uint8 value)
        value))
      (equal
       (sng11-to-uint8
        (sng11-to-uint8 value))
       (sng11-to-uint8 value))))))

(defun-sk sng11-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng11-is-uint64-p
       (sng11-to-uint64 value))
      (implies
       (sng11-is-uint64-p value)
       (equal
        (sng11-to-uint64 value)
        value))
      (equal
       (sng11-to-uint64
        (sng11-to-uint64 value))
       (sng11-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sng11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sng11-address-base address))
    (<= 0
        (sng11-address-offset address))
    (<=
     (+ (sng11-address-offset address)
        length)
     (sng11-allocation
      (sng11-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved verbatim.

(defun-sk sng11-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sng11-character-memory
       (sng11-shift address index))
      0)
     (< index count)
     (sng11-is-uint64-p index)
     (sng11-valid-rw-p
      (sng11-shift address 0)
      (+ 1 index)))))

(defun-sk sng11-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (sng11-is-sint8-p
       (sng11-character-memory
        (sng11-shift address position)))))))

(defun sng11-valid-bounded-string-p
    (address count)
  (or
   (sng11-valid-rw-p
    (sng11-shift address 0)
    (+ 1 count))
   (and
    (sng11-bounded-zero-witness-p
     address count)
    (sng11-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk sng11-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (sng11-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (sng11-character-memory
             (sng11-shift address 0))
            0))
          (equal
           (sng11-l-strnlen address count)
           0)
        (equal
         (sng11-to-uint64
          (+ 1
             (sng11-l-strnlen
              (sng11-shift address 1)
              (sng11-to-uint64
               (- count 1)))))
         (sng11-l-strnlen address count)))
      (sng11-is-uint64-p
       (sng11-l-strnlen address count))))))

;; The two source pointwise hypotheses retain their universal quantifiers over
;; all mathematical integers.

(defun-sk sng11-offset-prefix-equal-before-p
    (left right left-offset right-offset)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< (+ position left-offset)
          right-offset)
       (equal
        (sng11-character-memory
         (sng11-shift left position))
        (sng11-character-memory
         (sng11-shift right position))))))))

(defun-sk sng11-uint8-equality-reflects-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (iff
        (equal
         (sng11-to-uint8
          (sng11-character-memory
           (sng11-shift left position)))
         (sng11-to-uint8
          (sng11-character-memory
           (sng11-shift right position))))
        (equal
         (sng11-character-memory
          (sng11-shift left position))
         (sng11-character-memory
          (sng11-shift right position)))))))))

(defun-sk
    ntp4vc-strncmp-loop-inv-5-preserved-goal11-statement ()
  (forall
   (a1 a3 a i a2)
   (implies
    (and
     (sng11-address-p a1)
     (sng11-address-p a3)
     (sng11-address-p a)
     (integerp i)
     (sng11-address-p a2)
     (sng11-function-types-p)
     (sng11-address-order-law-p)
     (sng11-to-uint8-laws-p)
     (sng11-to-uint64-laws-p)
     (sng11-strnlen-laws-p))
    (let*
        ((x
          (sng11-character-memory a1))
         (x1
          (sng11-to-uint8 x))
         (x2
          (sng11-character-memory a3))
         (x3
          (sng11-address-offset a))
         (x4
          (+ i x3))
         (x5
          (sng11-address-offset a1))
         (x6
          (sng11-address-offset a2))
         (x7
          (sng11-address-offset a3))
         (x8
          (- x7 x6))
         (x9
          (sng11-character-memory
           (sng11-shift a2 x8)))
         (x10
          (sng11-character-memory
           (sng11-shift a x8)))
         (x12
          (- (+ i x3) x5))
         (x13
          (sng11-l-strnlen a i))
         (x14
          (sng11-l-strnlen a2 i))
         (x15
          (sng11-to-uint64
           (- (- (+ i x3) 1) x5))))
      (implies
       (and
        (not (equal x1 0))
        (equal
         (sng11-to-uint8 x2)
         x1)
        (not (equal x4 x5))
        (equal
         (+ x5 x6)
         (+ x3 x7))
        (equal x9 x10)
        (equal
         (+ x5
            (sng11-l-strnlen a1 x12))
         (+ x3 x13))
        (equal
         (+ x7
            (sng11-l-strnlen a3 x12))
         (+ x6 x14))
        (<= x3 x5)
        (<=
         (sng11-region
          (sng11-address-base a))
         0)
        (<=
         (sng11-region
          (sng11-address-base a2))
         0)
        (<= x5 x4)
        (sng11-linked-p)
        (sng11-sconst-p)
        (sng11-is-uint64-p i)
        (sng11-addr-le-p a a1)
        (sng11-addr-le-p a2 a3)
        (sng11-is-sint8-p x)
        (sng11-is-sint8-p x2)
        (sng11-valid-bounded-string-p
         a i)
        (sng11-valid-bounded-string-p
         a2 i)
        (sng11-is-uint64-p x12)
        (sng11-addr-le-p
         a1
         (sng11-shift a x13))
        (sng11-addr-le-p
         a3
         (sng11-shift a2 x14))
        (sng11-is-sint8-p x10)
        (sng11-is-sint8-p x9)
        (sng11-valid-bounded-string-p
         a1 x12)
        (sng11-valid-bounded-string-p
         a3 x12)
        (sng11-offset-prefix-equal-before-p
         a2 a x3 x5)
        (sng11-uint8-equality-reflects-p
         a2 a x14))
       (and
        (sng11-valid-bounded-string-p
         (sng11-shift a1 1)
         x15)
        (sng11-valid-bounded-string-p
         (sng11-shift a3 1)
         x15)))))))

(value-triple :itpeval-statement-checked)

:q
