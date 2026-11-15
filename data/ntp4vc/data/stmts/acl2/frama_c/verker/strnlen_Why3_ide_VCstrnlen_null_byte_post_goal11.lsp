;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strnlen_Why3_ide_VCstrnlen_null_byte_post_goal11:
;; the strnlen null-byte postcondition asserting that the byte at the
;; uint64-converted offset distance is zero, under the stated memory,
;; logical-length, bounded-string, address-order, and nonzero-prefix
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snnbp11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snnbp11-address-base (address)
  (car address))

(defun snnbp11-address-offset (address)
  (cdr address))

(defun snnbp11-shift (address amount)
  (cons
   (snnbp11-address-base address)
   (+ (snnbp11-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub snnbp11-character-memory (address) t)
(defstub snnbp11-allocation (index) t)
(defstub snnbp11-region (base) t)
(defstub snnbp11-addr-le-op (left right) t)
(defstub snnbp11-l-strnlen (address count) t)
(defstub snnbp11-to-uint64 (value) t)
(defstub snnbp11-linked-op () t)
(defstub snnbp11-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snnbp11-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (snnbp11-address-p address)
      (and
       (integerp
        (snnbp11-character-memory address))
       (implies
        (integerp count)
        (integerp
         (snnbp11-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (snnbp11-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snnbp11-region base)))
     (implies
      (integerp value)
      (integerp
       (snnbp11-to-uint64 value))))))

(defun snnbp11-addr-le-p (left right)
  (if (snnbp11-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk snnbp11-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (snnbp11-address-p left)
      (snnbp11-address-p right)
      (equal
       (snnbp11-address-base left)
       (snnbp11-address-base right)))
     (equal
      (snnbp11-addr-le-p left right)
      (<=
       (snnbp11-address-offset left)
       (snnbp11-address-offset right))))))

(defun snnbp11-linked-p ()
  (if (snnbp11-linked-op) t nil))

(defun snnbp11-sconst-p ()
  (if (snnbp11-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snnbp11-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snnbp11-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk snnbp11-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snnbp11-is-uint64-p
       (snnbp11-to-uint64 value))
      (implies
       (snnbp11-is-uint64-p value)
       (equal
        (snnbp11-to-uint64 value)
        value))
      (equal
       (snnbp11-to-uint64
        (snnbp11-to-uint64 value))
       (snnbp11-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snnbp11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snnbp11-address-base address))
    (<= 0
        (snnbp11-address-offset address))
    (<=
     (+ (snnbp11-address-offset address)
        length)
     (snnbp11-allocation
      (snnbp11-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved.

(defun-sk snnbp11-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snnbp11-character-memory
       (snnbp11-shift address index))
      0)
     (< index count)
     (snnbp11-is-uint64-p index)
     (snnbp11-valid-rw-p
      (snnbp11-shift address 0)
      (+ 1 index)))))

(defun-sk snnbp11-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snnbp11-is-sint8-p
       (snnbp11-character-memory
        (snnbp11-shift address position)))))))

(defun snnbp11-valid-bounded-string-p
    (address count)
  (or
   (snnbp11-valid-rw-p
    (snnbp11-shift address 0)
    (+ 1 count))
   (and
    (snnbp11-bounded-zero-witness-p
     address count)
    (snnbp11-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk snnbp11-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snnbp11-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snnbp11-character-memory
             (snnbp11-shift address 0))
            0))
          (equal
           (snnbp11-l-strnlen address count)
           0)
        (equal
         (snnbp11-to-uint64
          (+ 1
             (snnbp11-l-strnlen
              (snnbp11-shift address 1)
              (snnbp11-to-uint64
               (- count 1)))))
         (snnbp11-l-strnlen address count)))
      (snnbp11-is-uint64-p
       (snnbp11-l-strnlen address count))))))

;; The source nonzero-byte hypothesis retains its universal quantifier over
;; all mathematical integers.

(defun-sk snnbp11-nonzero-before-offset-p
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
         (snnbp11-character-memory
          (snnbp11-shift address position))
         0)))))))

(defun-sk
    ntp4vc-strnlen-null-byte-post-goal11-statement ()
  (forall
   (a a1 i1 i)
   (implies
    (and
     (snnbp11-address-p a)
     (snnbp11-address-p a1)
     (integerp i1)
     (integerp i)
     (snnbp11-function-types-p)
     (snnbp11-address-order-law-p)
     (snnbp11-to-uint64-laws-p)
     (snnbp11-strnlen-laws-p))
    (let*
        ((x
          (snnbp11-address-offset a))
         (x1
          (snnbp11-address-offset a1))
         (x2
          (- (+ i1 x1) x))
         (x3
          (snnbp11-l-strnlen a1 i1))
         (x4
          (+ i1 x1))
         (x5
          (snnbp11-character-memory
           (snnbp11-shift
            a1
            (snnbp11-to-uint64
             (- x x1))))))
      (implies
       (and
        (equal
         (snnbp11-character-memory
          (snnbp11-shift a1 i))
         0)
        (equal
         (+ x
            (snnbp11-l-strnlen a x2))
         (+ x1 x3))
        (<= 0 i)
        (<= i i1)
        (<= x1 x)
        (<=
         (snnbp11-region
          (snnbp11-address-base a1))
         0)
        (<= x x4)
        (snnbp11-linked-p)
        (snnbp11-sconst-p)
        (snnbp11-is-uint64-p i1)
        (snnbp11-addr-le-p a1 a)
        (snnbp11-valid-bounded-string-p
         a1 i1)
        (snnbp11-is-uint64-p x2)
        (snnbp11-addr-le-p
         a
         (snnbp11-shift a1 x3))
        (snnbp11-valid-bounded-string-p
         a x2)
        (snnbp11-is-sint8-p x5)
        (or
         (equal
          (snnbp11-character-memory a)
          0)
         (equal x4 x))
        (snnbp11-nonzero-before-offset-p
         a1 x1 x))
       (equal x5 0))))))

(value-triple :itpeval-statement-checked)

:q
