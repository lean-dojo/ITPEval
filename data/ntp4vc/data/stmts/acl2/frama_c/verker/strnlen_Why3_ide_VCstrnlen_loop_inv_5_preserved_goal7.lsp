;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strnlen_Why3_ide_VCstrnlen_loop_inv_5_preserved_goal7:
;; preservation of the strnlen loop's logical-length equality after advancing
;; the current address by one and decrementing its uint64 count, under the
;; stated offset, memory, character-range, address-order,
;; bounded-string-validity, and nonzero-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snli5g7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snli5g7-address-base (address)
  (car address))

(defun snli5g7-address-offset (address)
  (cdr address))

(defun snli5g7-shift (address amount)
  (cons
   (snli5g7-address-base address)
   (+ (snli5g7-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strnlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub snli5g7-character-memory (address) t)
(defstub snli5g7-allocation (index) t)
(defstub snli5g7-region (base) t)
(defstub snli5g7-addr-le-op (left right) t)
(defstub snli5g7-l-strnlen (address count) t)
(defstub snli5g7-to-uint64 (value) t)
(defstub snli5g7-linked-op () t)
(defstub snli5g7-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snli5g7-function-types-p ()
  (forall (address index base value count)
    (and
     (implies
      (snli5g7-address-p address)
      (and
       (integerp
        (snli5g7-character-memory address))
       (implies
        (integerp count)
        (integerp
         (snli5g7-l-strnlen address count)))))
     (implies
      (integerp index)
      (integerp
       (snli5g7-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snli5g7-region base)))
     (implies
      (integerp value)
      (integerp
       (snli5g7-to-uint64 value))))))

(defun snli5g7-addr-le-p (left right)
  (if (snli5g7-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk snli5g7-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (snli5g7-address-p left)
      (snli5g7-address-p right)
      (equal
       (snli5g7-address-base left)
       (snli5g7-address-base right)))
     (equal
      (snli5g7-addr-le-p left right)
      (<=
       (snli5g7-address-offset left)
       (snli5g7-address-offset right))))))

(defun snli5g7-linked-p ()
  (if (snli5g7-linked-op) t nil))

(defun snli5g7-sconst-p ()
  (if (snli5g7-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snli5g7-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snli5g7-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk snli5g7-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snli5g7-is-uint64-p
       (snli5g7-to-uint64 value))
      (implies
       (snli5g7-is-uint64-p value)
       (equal
        (snli5g7-to-uint64 value)
        value))
      (equal
       (snli5g7-to-uint64
        (snli5g7-to-uint64 value))
       (snli5g7-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snli5g7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snli5g7-address-base address))
    (<= 0
        (snli5g7-address-offset address))
    (<=
     (+ (snli5g7-address-offset address)
        length)
     (snli5g7-allocation
      (snli5g7-address-base address))))))

;; Exact unfolding of A_Strnlen.p_valid_strn. The source disjunction and the
;; existential and universal quantifier scopes are preserved.

(defun-sk snli5g7-bounded-zero-witness-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snli5g7-character-memory
       (snli5g7-shift address index))
      0)
     (< index count)
     (snli5g7-is-uint64-p index)
     (snli5g7-valid-rw-p
      (snli5g7-shift address 0)
      (+ 1 index)))))

(defun-sk snli5g7-bounded-chars-sint8-through-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snli5g7-is-sint8-p
       (snli5g7-character-memory
        (snli5g7-shift address position)))))))

(defun snli5g7-valid-bounded-string-p
    (address count)
  (or
   (snli5g7-valid-rw-p
    (snli5g7-shift address 0)
    (+ 1 count))
   (and
    (snli5g7-bounded-zero-witness-p
     address count)
    (snli5g7-bounded-chars-sint8-through-p
     address count))))

;; Universal closures of A_Strnlen.fix_l_strnlen and Q_TL_strnlen.

(defun-sk snli5g7-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snli5g7-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snli5g7-character-memory
             (snli5g7-shift address 0))
            0))
          (equal
           (snli5g7-l-strnlen address count)
           0)
        (equal
         (snli5g7-to-uint64
          (+ 1
             (snli5g7-l-strnlen
              (snli5g7-shift address 1)
              (snli5g7-to-uint64
               (- count 1)))))
         (snli5g7-l-strnlen address count)))
      (snli5g7-is-uint64-p
       (snli5g7-l-strnlen address count))))))

;; The source nonzero-byte hypothesis retains its universal quantifier over
;; all mathematical integers.

(defun-sk snli5g7-nonzero-before-offset-p
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
         (snli5g7-character-memory
          (snli5g7-shift address position))
         0)))))))

(defun-sk
    ntp4vc-strnlen-loop-inv-5-preserved-goal7-statement ()
  (forall
   (a a1 i)
   (implies
    (and
     (snli5g7-address-p a)
     (snli5g7-address-p a1)
     (integerp i)
     (snli5g7-function-types-p)
     (snli5g7-address-order-law-p)
     (snli5g7-to-uint64-laws-p)
     (snli5g7-strnlen-laws-p))
    (let*
        ((x
          (snli5g7-character-memory a))
         (x1
          (snli5g7-address-offset a1))
         (x2
          (snli5g7-address-offset a))
         (x3
          (- (+ i x2) x1))
         (x4
          (snli5g7-l-strnlen a1 x3))
         (x5
          (+ x1 x4)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x 0))
        (equal
         x5
         (+ x2
            (snli5g7-l-strnlen a i)))
        (<= 0 i)
        (<= x1 x2)
        (<=
         (snli5g7-region
          (snli5g7-address-base a1))
         0)
        (snli5g7-linked-p)
        (snli5g7-sconst-p)
        (snli5g7-is-uint64-p i)
        (snli5g7-addr-le-p a1 a)
        (snli5g7-is-sint8-p x)
        (snli5g7-valid-bounded-string-p
         a i)
        (snli5g7-is-uint64-p x3)
        (snli5g7-valid-bounded-string-p
         a1 x3)
        (snli5g7-addr-le-p
         a
         (snli5g7-shift a1 x4))
        (snli5g7-nonzero-before-offset-p
         a1 x1 x2))
       (equal
        x5
        (+ 1
           x2
           (snli5g7-l-strnlen
            (snli5g7-shift a 1)
            (snli5g7-to-uint64
             (- i 1))))))))))

(value-triple :itpeval-statement-checked)

:q
