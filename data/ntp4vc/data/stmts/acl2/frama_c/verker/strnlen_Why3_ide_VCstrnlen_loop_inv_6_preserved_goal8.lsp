;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strnlen_Why3_ide_VCstrnlen_loop_inv_6_preserved_goal8:
;; the strnlen loop's nonzero-prefix invariant implies that the byte at the
;; current integer index is nonzero, under the stated offset, memory,
;; character-range, address-order, logical-length, and bounded-string-validity
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snli6g8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snli6g8-address-base (address)
  (car address))

(defun snli6g8-address-offset (address)
  (cdr address))

(defun snli6g8-shift (address amount)
  (cons
   (snli6g8-address-base address)
   (+ (snli6g8-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub snli6g8-character-memory (address) t)
(defstub snli6g8-allocation (index) t)
(defstub snli6g8-region (base) t)
(defstub snli6g8-addr-le-op (left right) t)
(defstub snli6g8-l-strnlen (address count) t)
(defstub snli6g8-to-uint64 (value) t)
(defstub snli6g8-linked-op () t)
(defstub snli6g8-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snli6g8-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (snli6g8-address-p address)
      (and
       (integerp
        (snli6g8-character-memory address))
       (implies
        (integerp count)
        (integerp
         (snli6g8-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (snli6g8-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snli6g8-region base)))
     (implies
      (integerp value)
      (integerp
       (snli6g8-to-uint64 value))))))

(defun snli6g8-addr-le-p (left right)
  (if (snli6g8-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk snli6g8-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (snli6g8-address-p left)
      (snli6g8-address-p right)
      (equal
       (snli6g8-address-base left)
       (snli6g8-address-base right)))
     (equal
      (snli6g8-addr-le-p left right)
      (<=
       (snli6g8-address-offset left)
       (snli6g8-address-offset right))))))

(defun snli6g8-linked-p ()
  (if (snli6g8-linked-op) t nil))

(defun snli6g8-sconst-p ()
  (if (snli6g8-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snli6g8-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snli6g8-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk snli6g8-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snli6g8-is-uint64-p
       (snli6g8-to-uint64 value))
      (implies
       (snli6g8-is-uint64-p value)
       (equal
        (snli6g8-to-uint64 value)
        value))
      (equal
       (snli6g8-to-uint64
        (snli6g8-to-uint64 value))
       (snli6g8-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snli6g8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snli6g8-address-base address))
    (<= 0
        (snli6g8-address-offset address))
    (<=
     (+ (snli6g8-address-offset address)
        length)
     (snli6g8-allocation
      (snli6g8-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved.

(defun-sk snli6g8-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snli6g8-character-memory
       (snli6g8-shift address index))
      0)
     (< index count)
     (snli6g8-is-uint64-p index)
     (snli6g8-valid-rw-p
      (snli6g8-shift address 0)
      (+ 1 index)))))

(defun-sk snli6g8-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snli6g8-is-sint8-p
       (snli6g8-character-memory
        (snli6g8-shift address position)))))))

(defun snli6g8-valid-bounded-string-p
    (address count)
  (or
   (snli6g8-valid-rw-p
    (snli6g8-shift address 0)
    (+ 1 count))
   (and
    (snli6g8-bounded-zero-witness-p
     address count)
    (snli6g8-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk snli6g8-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snli6g8-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snli6g8-character-memory
             (snli6g8-shift address 0))
            0))
          (equal
           (snli6g8-l-strnlen address count)
           0)
        (equal
         (snli6g8-to-uint64
          (+ 1
             (snli6g8-l-strnlen
              (snli6g8-shift address 1)
              (snli6g8-to-uint64
               (- count 1)))))
         (snli6g8-l-strnlen address count)))
      (snli6g8-is-uint64-p
       (snli6g8-l-strnlen address count))))))

;; The source nonzero-byte hypothesis retains its universal quantifier over
;; all mathematical integers.

(defun-sk snli6g8-nonzero-before-offset-p
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
         (snli6g8-character-memory
          (snli6g8-shift address position))
         0)))))))

(defun-sk
    ntp4vc-strnlen-loop-inv-6-preserved-goal8-statement ()
  (forall
   (a a1 i1 i)
   (implies
    (and
     (snli6g8-address-p a)
     (snli6g8-address-p a1)
     (integerp i1)
     (integerp i)
     (snli6g8-function-types-p)
     (snli6g8-address-order-law-p)
     (snli6g8-to-uint64-laws-p)
     (snli6g8-strnlen-laws-p))
    (let*
        ((x
          (snli6g8-character-memory a))
         (x1
          (snli6g8-address-offset a1))
         (x2
          (snli6g8-address-offset a))
         (x3
          (- (+ i1 x2) x1))
         (x4
          (snli6g8-l-strnlen a1 x3)))
      (implies
       (and
        (not (equal i1 0))
        (not (equal x 0))
        (equal
         (+ x1 x4)
         (+ x2
            (snli6g8-l-strnlen a i1)))
        (<= 0 i)
        (<= 0 i1)
        (<= x1 x2)
        (<=
         (snli6g8-region
          (snli6g8-address-base a1))
         0)
        (<= (+ i x1) x2)
        (snli6g8-linked-p)
        (snli6g8-sconst-p)
        (snli6g8-is-uint64-p i1)
        (snli6g8-addr-le-p a1 a)
        (snli6g8-is-sint8-p x)
        (snli6g8-valid-bounded-string-p
         a i1)
        (snli6g8-is-uint64-p x3)
        (snli6g8-valid-bounded-string-p
         a1 x3)
        (snli6g8-addr-le-p
         a
         (snli6g8-shift a1 x4))
        (snli6g8-nonzero-before-offset-p
         a1 x1 x2))
       (not
        (equal
         (snli6g8-character-memory
          (snli6g8-shift a1 i))
         0)))))))

(value-triple :itpeval-statement-checked)

:q
