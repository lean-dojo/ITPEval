;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strcmp_Why3_ide_VCstrcmp_loop_inv_3_preserved_goal5:
;; preservation of the strcmp loop invariant relating two valid strings,
;; their offsets, byte values, and pointwise character equality.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun scg5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun scg5-address-base (address)
  (car address))

(defun scg5-address-offset (address)
  (cdr address))

(defun scg5-shift (address amount)
  (cons
   (scg5-address-base address)
   (+ (scg5-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strlen, logical strncmp, C integer conversions,
;; linkedness, and constancy symbols.

(defstub scg5-character-memory (address) t)
(defstub scg5-allocation (index) t)
(defstub scg5-region (base) t)
(defstub scg5-addr-le-op (left right) t)
(defstub scg5-l-strlen (address) t)
(defstub scg5-l-strncmp (left right count) t)
(defstub scg5-to-uint8 (value) t)
(defstub scg5-to-uint64 (value) t)
(defstub scg5-linked-op () t)
(defstub scg5-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk scg5-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (scg5-address-p address)
      (and
       (integerp
        (scg5-character-memory address))
       (integerp
        (scg5-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (scg5-allocation index)))
     (implies
      (integerp base)
      (integerp
       (scg5-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (scg5-to-uint8 value))
       (integerp
        (scg5-to-uint64 value))))
     (implies
      (and
       (scg5-address-p left)
       (scg5-address-p right)
       (integerp count))
      (integerp
       (scg5-l-strncmp left right count))))))

(defun scg5-addr-le-p (left right)
  (if (scg5-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk scg5-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (scg5-address-p left)
      (scg5-address-p right)
      (equal
       (scg5-address-base left)
       (scg5-address-base right)))
     (equal
      (scg5-addr-le-p left right)
      (<=
       (scg5-address-offset left)
       (scg5-address-offset right))))))

(defun scg5-linked-p ()
  (if (scg5-linked-op) t nil))

(defun scg5-sconst-p ()
  (if (scg5-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun scg5-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun scg5-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun scg5-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and the logical strlen recurrence.

(defun-sk scg5-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg5-is-uint8-p
       (scg5-to-uint8 value))
      (implies
       (scg5-is-uint8-p value)
       (equal
        (scg5-to-uint8 value)
        value))
      (equal
       (scg5-to-uint8
        (scg5-to-uint8 value))
       (scg5-to-uint8 value))))))

(defun-sk scg5-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg5-is-uint64-p
       (scg5-to-uint64 value))
      (implies
       (scg5-is-uint64-p value)
       (equal
        (scg5-to-uint64 value)
        value))
      (equal
       (scg5-to-uint64
        (scg5-to-uint64 value))
       (scg5-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun scg5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (scg5-address-base address))
    (<= 0
        (scg5-address-offset address))
    (<=
     (+ (scg5-address-offset address)
        length)
     (scg5-allocation
      (scg5-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk scg5-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (scg5-is-sint8-p
       (scg5-character-memory
        (scg5-shift address position)))))))

(defun-sk scg5-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (scg5-character-memory
       (scg5-shift address index))
      0)
     (scg5-is-uint64-p index)
     (scg5-valid-rw-p
      (scg5-shift address 0)
      (+ 1 index))
     (scg5-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk scg5-strlen-laws-p ()
  (forall (address)
    (implies
     (scg5-address-p address)
     (and
      (if
          (equal
           (scg5-character-memory
            (scg5-shift address 0))
           0)
          (equal
           (scg5-l-strlen address)
           0)
        (equal
         (scg5-to-uint64
          (+ 1
             (scg5-l-strlen
              (scg5-shift address 1))))
         (scg5-l-strlen address)))
      (scg5-is-uint64-p
       (scg5-l-strlen address))))))

;; Exact definitions of A_StrCmp.l_cmp and A_StrCmp.l_strcmp.

(defun scg5-l-cmp (left right)
  (if (equal right left)
      0
    (if (< left right) -1 1)))

(defun scg5-l-strcmp (left right)
  (scg5-l-strncmp
   left
   right
   (scg5-l-strlen left)))

;; Universal closure of A_StrCmp.fix_l_strncmp_1'.

(defun-sk scg5-strncmp-law-p ()
  (forall (left right count)
    (implies
     (and
      (scg5-address-p left)
      (scg5-address-p right)
      (integerp count))
     (if
         (equal count -1)
         (equal
          (scg5-l-strncmp left right count)
          0)
       (if
           (equal
            (scg5-character-memory
             (scg5-shift right 0))
            (scg5-character-memory
             (scg5-shift left 0)))
           (equal
            (scg5-l-strncmp
             (scg5-shift left 1)
             (scg5-shift right 1)
             (- count 1))
            (scg5-l-strncmp left right count))
         (equal
          (scg5-l-cmp
           (scg5-to-uint8
            (scg5-character-memory
             (scg5-shift left 0)))
           (scg5-to-uint8
            (scg5-character-memory
             (scg5-shift right 0))))
          (scg5-l-strncmp left right count)))))))

;; The source equality of universally quantified prefix properties is kept as
;; a biconditional between predicates quantified over every mathematical
;; integer.

(defun-sk scg5-uint8-prefix-equal-through-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (<= position bound)
       (equal
        (scg5-to-uint8
         (scg5-character-memory
          (scg5-shift left position)))
        (scg5-to-uint8
         (scg5-character-memory
          (scg5-shift right position)))))))))

(defun-sk scg5-raw-prefix-equal-through-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (<= position bound)
       (equal
        (scg5-character-memory
         (scg5-shift left position))
        (scg5-character-memory
         (scg5-shift right position))))))))

;; The final loop hypothesis retains its universal quantifier and strict
;; offset bound over all mathematical integers.

(defun-sk scg5-raw-prefix-equal-before-offset-p
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
        (scg5-character-memory
         (scg5-shift left position))
        (scg5-character-memory
         (scg5-shift right position))))))))

(defun-sk
    ntp4vc-strcmp-loop-inv-3-preserved-goal5-statement ()
  (forall
   (a a2 a3 a1)
   (implies
    (and
     (scg5-address-p a)
     (scg5-address-p a2)
     (scg5-address-p a3)
     (scg5-address-p a1)
     (scg5-function-types-p)
     (scg5-address-order-law-p)
     (scg5-to-uint8-laws-p)
     (scg5-to-uint64-laws-p)
     (scg5-strlen-laws-p)
     (scg5-strncmp-law-p))
    (let*
        ((x
          (scg5-character-memory a))
         (x1
          (scg5-to-uint8 x))
         (x2
          (scg5-character-memory a2))
         (x3
          (scg5-address-offset a2))
         (x4
          (scg5-address-offset a3))
         (x5
          (scg5-l-strlen a3))
         (x6
          (- x3 x4))
         (x7
          (scg5-character-memory
           (scg5-shift a3 x6)))
         (x8
          (scg5-character-memory
           (scg5-shift a1 x6)))
         (a4
          (scg5-shift
           a1
           (scg5-l-strlen a1)))
         (a5
          (scg5-shift a 1)))
      (implies
       (and
        (not (equal x1 0))
        (equal
         (scg5-to-uint8 x2)
         x1)
        (equal
         (scg5-l-strcmp a3 a1)
         (scg5-l-strcmp a2 a))
        (equal
         (+ (scg5-address-offset a1)
            x3)
         (+ (scg5-address-offset a)
            x4))
        (equal
         (+ x4 x5)
         (+ x3
            (scg5-l-strlen a2)))
        (equal x7 x8)
        (iff
         (scg5-uint8-prefix-equal-through-p
          a3 a1 x5)
         (scg5-raw-prefix-equal-through-p
          a3 a1 x5))
        (<=
         (scg5-region
          (scg5-address-base a1))
         0)
        (<=
         (scg5-region
          (scg5-address-base a3))
         0)
        (scg5-linked-p)
        (scg5-sconst-p)
        (scg5-addr-le-p a1 a)
        (scg5-addr-le-p a3 a2)
        (scg5-is-sint8-p x)
        (scg5-is-sint8-p x2)
        (scg5-valid-string-p a)
        (scg5-valid-string-p a1)
        (scg5-valid-string-p a2)
        (scg5-valid-string-p a3)
        (scg5-addr-le-p a a4)
        (scg5-addr-le-p
         a2
         (scg5-shift a3 x5))
        (scg5-is-sint8-p x8)
        (scg5-is-sint8-p x7)
        (scg5-raw-prefix-equal-before-offset-p
         a3 a1 x4 x3))
       (and
        (scg5-addr-le-p a1 a5)
        (scg5-addr-le-p a5 a4)))))))

(value-triple :itpeval-statement-checked)

:q
