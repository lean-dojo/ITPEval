;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strcmp_Why3_ide_VCstrcmp_loop_inv_preserved_goal2:
;; preservation of valid strings after advancing both strcmp pointers by one,
;; under the stated address, string, byte, and prefix-equality hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun scg2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun scg2-address-base (address)
  (car address))

(defun scg2-address-offset (address)
  (cdr address))

(defun scg2-shift (address amount)
  (cons
   (scg2-address-base address)
   (+ (scg2-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strlen, logical strncmp, C integer conversions,
;; linkedness, and constancy symbols.

(defstub scg2-character-memory (address) t)
(defstub scg2-allocation (index) t)
(defstub scg2-region (base) t)
(defstub scg2-addr-le-op (left right) t)
(defstub scg2-l-strlen (address) t)
(defstub scg2-l-strncmp (left right count) t)
(defstub scg2-to-uint8 (value) t)
(defstub scg2-to-sint8 (value) t)
(defstub scg2-to-uint64 (value) t)
(defstub scg2-to-sint64 (value) t)
(defstub scg2-linked-op () t)
(defstub scg2-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk scg2-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (scg2-address-p address)
      (and
       (integerp
        (scg2-character-memory address))
       (integerp
        (scg2-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (scg2-allocation index)))
     (implies
      (integerp base)
      (integerp
       (scg2-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (scg2-to-uint8 value))
       (integerp
        (scg2-to-sint8 value))
       (integerp
        (scg2-to-uint64 value))
       (integerp
        (scg2-to-sint64 value))))
     (implies
      (and
       (scg2-address-p left)
       (scg2-address-p right)
       (integerp count))
      (integerp
       (scg2-l-strncmp left right count))))))

(defun scg2-addr-le-p (left right)
  (if (scg2-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk scg2-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (scg2-address-p left)
      (scg2-address-p right)
      (equal
       (scg2-address-base left)
       (scg2-address-base right)))
     (equal
      (scg2-addr-le-p left right)
      (<=
       (scg2-address-offset left)
       (scg2-address-offset right))))))

(defun scg2-linked-p ()
  (if (scg2-linked-op) t nil))

(defun scg2-sconst-p ()
  (if (scg2-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun scg2-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun scg2-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun scg2-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun scg2-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and the logical strlen recurrence.

(defun-sk scg2-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg2-is-uint8-p
       (scg2-to-uint8 value))
      (implies
       (scg2-is-uint8-p value)
       (equal
        (scg2-to-uint8 value)
        value))
      (equal
       (scg2-to-uint8
       (scg2-to-uint8 value))
       (scg2-to-uint8 value))))))

(defun-sk scg2-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg2-is-sint8-p
       (scg2-to-sint8 value))
      (implies
       (scg2-is-sint8-p value)
       (equal
        (scg2-to-sint8 value)
        value))
      (equal
       (scg2-to-sint8
        (scg2-to-sint8 value))
       (scg2-to-sint8 value))))))

(defun-sk scg2-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg2-is-uint64-p
       (scg2-to-uint64 value))
      (implies
       (scg2-is-uint64-p value)
       (equal
        (scg2-to-uint64 value)
        value))
      (equal
       (scg2-to-uint64
       (scg2-to-uint64 value))
       (scg2-to-uint64 value))))))

(defun-sk scg2-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg2-is-sint64-p
       (scg2-to-sint64 value))
      (implies
       (scg2-is-sint64-p value)
       (equal
        (scg2-to-sint64 value)
        value))
      (equal
       (scg2-to-sint64
        (scg2-to-sint64 value))
       (scg2-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk scg2-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (scg2-to-sint8
        (scg2-to-uint8 value))
       (scg2-to-sint8 value))
      (equal
       (scg2-to-sint64
        (scg2-to-uint64 value))
       (scg2-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun scg2-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (scg2-address-base address))
    (<= 0
        (scg2-address-offset address))
    (<=
     (+ (scg2-address-offset address)
        length)
     (scg2-allocation
      (scg2-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk scg2-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (scg2-is-sint8-p
       (scg2-character-memory
        (scg2-shift address position)))))))

(defun-sk scg2-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (scg2-character-memory
       (scg2-shift address index))
      0)
     (scg2-is-uint64-p index)
     (scg2-valid-rw-p
      (scg2-shift address 0)
      (+ 1 index))
     (scg2-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk scg2-strlen-laws-p ()
  (forall (address)
    (implies
     (scg2-address-p address)
     (and
      (if
          (equal
           (scg2-character-memory
            (scg2-shift address 0))
           0)
          (equal
           (scg2-l-strlen address)
           0)
        (equal
         (scg2-to-uint64
          (+ 1
             (scg2-l-strlen
              (scg2-shift address 1))))
         (scg2-l-strlen address)))
      (scg2-is-uint64-p
       (scg2-l-strlen address))))))

;; Exact definitions of A_StrCmp.l_cmp and A_StrCmp.l_strcmp.

(defun scg2-l-cmp (left right)
  (if (equal right left)
      0
    (if (< left right) -1 1)))

(defun scg2-l-strcmp (left right)
  (scg2-l-strncmp
   left
   right
   (scg2-l-strlen left)))

;; Universal closure of A_StrCmp.fix_l_strncmp_1'.

(defun-sk scg2-strncmp-law-p ()
  (forall (left right count)
    (implies
     (and
      (scg2-address-p left)
      (scg2-address-p right)
      (integerp count))
     (if
         (equal count -1)
         (equal
          (scg2-l-strncmp left right count)
          0)
       (if
           (equal
            (scg2-character-memory
             (scg2-shift right 0))
            (scg2-character-memory
             (scg2-shift left 0)))
           (equal
            (scg2-l-strncmp
             (scg2-shift left 1)
             (scg2-shift right 1)
             (- count 1))
            (scg2-l-strncmp left right count))
         (equal
          (scg2-l-cmp
           (scg2-to-uint8
            (scg2-character-memory
             (scg2-shift left 0)))
           (scg2-to-uint8
            (scg2-character-memory
             (scg2-shift right 0))))
          (scg2-l-strncmp left right count)))))))

;; The source equality of universally quantified prefix properties is kept as
;; a biconditional between predicates quantified over every mathematical
;; integer.

(defun-sk scg2-uint8-prefix-equal-through-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (<= position bound)
       (equal
        (scg2-to-uint8
         (scg2-character-memory
          (scg2-shift left position)))
        (scg2-to-uint8
         (scg2-character-memory
          (scg2-shift right position)))))))))

(defun-sk scg2-raw-prefix-equal-through-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (<= position bound)
       (equal
        (scg2-character-memory
         (scg2-shift left position))
        (scg2-character-memory
         (scg2-shift right position))))))))

;; The final loop hypothesis retains its universal quantifier and strict
;; offset bound over all mathematical integers.

(defun-sk scg2-raw-prefix-equal-before-offset-p
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
        (scg2-character-memory
         (scg2-shift left position))
        (scg2-character-memory
         (scg2-shift right position))))))))

(defun-sk
    ntp4vc-strcmp-loop-inv-preserved-goal2-statement ()
  (forall
   (a a2 a3 a1)
   (implies
    (and
     (scg2-address-p a)
     (scg2-address-p a2)
     (scg2-address-p a3)
     (scg2-address-p a1)
     (scg2-function-types-p)
     (scg2-address-order-law-p)
     (scg2-to-uint8-laws-p)
     (scg2-to-sint8-laws-p)
     (scg2-to-uint64-laws-p)
     (scg2-to-sint64-laws-p)
     (scg2-signed-unsigned-projection-laws-p)
     (scg2-strlen-laws-p)
     (scg2-strncmp-law-p))
    (let*
        ((x
          (scg2-character-memory a))
         (x1
          (scg2-to-uint8 x))
         (x2
          (scg2-character-memory a2))
         (x3
          (scg2-address-offset a2))
         (x4
          (scg2-address-offset a3))
         (x5
          (scg2-l-strlen a3))
         (x6
          (- x3 x4))
         (x7
          (scg2-character-memory
           (scg2-shift a3 x6)))
         (x8
          (scg2-character-memory
           (scg2-shift a1 x6))))
      (implies
       (and
        (not (equal x1 0))
        (equal
         (scg2-to-uint8 x2)
         x1)
        (equal
         (scg2-l-strcmp a3 a1)
         (scg2-l-strcmp a2 a))
        (equal
         (+ (scg2-address-offset a1)
            x3)
         (+ (scg2-address-offset a)
            x4))
        (equal
         (+ x4 x5)
         (+ x3
            (scg2-l-strlen a2)))
        (equal x7 x8)
        (iff
         (scg2-uint8-prefix-equal-through-p
          a3 a1 x5)
         (scg2-raw-prefix-equal-through-p
          a3 a1 x5))
        (<=
         (scg2-region
          (scg2-address-base a1))
         0)
        (<=
         (scg2-region
          (scg2-address-base a3))
         0)
        (scg2-linked-p)
        (scg2-sconst-p)
        (scg2-addr-le-p a1 a)
        (scg2-addr-le-p a3 a2)
        (scg2-is-sint8-p x)
        (scg2-is-sint8-p x2)
        (scg2-valid-string-p a)
        (scg2-valid-string-p a1)
        (scg2-valid-string-p a2)
        (scg2-valid-string-p a3)
        (scg2-addr-le-p
         a
         (scg2-shift
          a1
          (scg2-l-strlen a1)))
        (scg2-addr-le-p
         a2
         (scg2-shift a3 x5))
        (scg2-is-sint8-p x8)
        (scg2-is-sint8-p x7)
        (scg2-raw-prefix-equal-before-offset-p
         a3 a1 x4 x3))
       (and
        (scg2-valid-string-p
         (scg2-shift a 1))
        (scg2-valid-string-p
         (scg2-shift a2 1))))))))

(value-triple :itpeval-statement-checked)

:q
