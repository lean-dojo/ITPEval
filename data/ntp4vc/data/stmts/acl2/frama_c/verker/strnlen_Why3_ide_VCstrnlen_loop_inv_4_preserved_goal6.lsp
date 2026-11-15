;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strnlen_Why3_ide_VCstrnlen_loop_inv_4_preserved_goal6:
;; preservation of bounded-string validity after advancing the current
;; strnlen address by one and decrementing its uint64 count, under the stated
;; offset, memory, character-range, address-order, logical-length, and
;; nonzero-prefix hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snli4g6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snli4g6-address-base (address)
  (car address))

(defun snli4g6-address-offset (address)
  (cdr address))

(defun snli4g6-shift (address amount)
  (cons
   (snli4g6-address-base address)
   (+ (snli4g6-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub snli4g6-character-memory (address) t)
(defstub snli4g6-allocation (index) t)
(defstub snli4g6-region (base) t)
(defstub snli4g6-addr-le-op (left right) t)
(defstub snli4g6-l-strnlen (address count) t)
(defstub snli4g6-to-uint64 (value) t)
(defstub snli4g6-linked-op () t)
(defstub snli4g6-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snli4g6-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (snli4g6-address-p address)
      (and
       (integerp
        (snli4g6-character-memory address))
       (implies
        (integerp count)
        (integerp
         (snli4g6-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (snli4g6-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snli4g6-region base)))
     (implies
      (integerp value)
      (integerp
       (snli4g6-to-uint64 value))))))

(defun snli4g6-addr-le-p (left right)
  (if (snli4g6-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk snli4g6-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (snli4g6-address-p left)
      (snli4g6-address-p right)
      (equal
       (snli4g6-address-base left)
       (snli4g6-address-base right)))
     (equal
      (snli4g6-addr-le-p left right)
      (<=
       (snli4g6-address-offset left)
       (snli4g6-address-offset right))))))

(defun snli4g6-linked-p ()
  (if (snli4g6-linked-op) t nil))

(defun snli4g6-sconst-p ()
  (if (snli4g6-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snli4g6-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snli4g6-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk snli4g6-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snli4g6-is-uint64-p
       (snli4g6-to-uint64 value))
      (implies
       (snli4g6-is-uint64-p value)
       (equal
        (snli4g6-to-uint64 value)
        value))
      (equal
       (snli4g6-to-uint64
        (snli4g6-to-uint64 value))
       (snli4g6-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snli4g6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snli4g6-address-base address))
    (<= 0
        (snli4g6-address-offset address))
    (<=
     (+ (snli4g6-address-offset address)
        length)
     (snli4g6-allocation
      (snli4g6-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved.

(defun-sk snli4g6-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snli4g6-character-memory
       (snli4g6-shift address index))
      0)
     (< index count)
     (snli4g6-is-uint64-p index)
     (snli4g6-valid-rw-p
      (snli4g6-shift address 0)
      (+ 1 index)))))

(defun-sk snli4g6-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snli4g6-is-sint8-p
       (snli4g6-character-memory
        (snli4g6-shift address position)))))))

(defun snli4g6-valid-bounded-string-p
    (address count)
  (or
   (snli4g6-valid-rw-p
    (snli4g6-shift address 0)
    (+ 1 count))
   (and
    (snli4g6-bounded-zero-witness-p
     address count)
    (snli4g6-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk snli4g6-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snli4g6-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snli4g6-character-memory
             (snli4g6-shift address 0))
            0))
          (equal
           (snli4g6-l-strnlen address count)
           0)
        (equal
         (snli4g6-to-uint64
          (+ 1
             (snli4g6-l-strnlen
              (snli4g6-shift address 1)
              (snli4g6-to-uint64
               (- count 1)))))
         (snli4g6-l-strnlen address count)))
      (snli4g6-is-uint64-p
       (snli4g6-l-strnlen address count))))))

;; The source nonzero-byte hypothesis retains its universal quantifier over
;; all mathematical integers.

(defun-sk snli4g6-nonzero-before-offset-p
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
         (snli4g6-character-memory
          (snli4g6-shift address position))
         0)))))))

(defun-sk
    ntp4vc-strnlen-loop-inv-4-preserved-goal6-statement ()
  (forall
   (a a1 i)
   (implies
    (and
     (snli4g6-address-p a)
     (snli4g6-address-p a1)
     (integerp i)
     (snli4g6-function-types-p)
     (snli4g6-address-order-law-p)
     (snli4g6-to-uint64-laws-p)
     (snli4g6-strnlen-laws-p))
    (let*
        ((x
          (snli4g6-character-memory a))
         (x1
          (snli4g6-address-offset a1))
         (x2
          (snli4g6-address-offset a))
         (x3
          (- (+ i x2) x1))
         (x4
          (snli4g6-l-strnlen a1 x3)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x 0))
        (equal
         (+ x1 x4)
         (+ x2
            (snli4g6-l-strnlen a i)))
        (<= 0 i)
        (<= x1 x2)
        (<=
         (snli4g6-region
          (snli4g6-address-base a1))
         0)
        (snli4g6-linked-p)
        (snli4g6-sconst-p)
        (snli4g6-is-uint64-p i)
        (snli4g6-addr-le-p a1 a)
        (snli4g6-is-sint8-p x)
        (snli4g6-valid-bounded-string-p
         a i)
        (snli4g6-is-uint64-p x3)
        (snli4g6-valid-bounded-string-p
         a1 x3)
        (snli4g6-addr-le-p
         a
         (snli4g6-shift a1 x4))
        (snli4g6-nonzero-before-offset-p
         a1 x1 x2))
       (snli4g6-valid-bounded-string-p
        (snli4g6-shift a 1)
        (snli4g6-to-uint64
         (- i 1))))))))

(value-triple :itpeval-statement-checked)

:q
