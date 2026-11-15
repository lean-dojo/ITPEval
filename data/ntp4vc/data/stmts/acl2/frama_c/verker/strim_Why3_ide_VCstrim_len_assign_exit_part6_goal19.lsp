;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strim_Why3_ide_VCstrim_len_assign_exit_part6_goal19:
;; a strim verification condition asserting inclusion of the byte after the
;; current address in the original string region, under the stated string,
;; memory-validity, address-order, whitespace, and no-null-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun slg19-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun slg19-address-base (address)
  (car address))

(defun slg19-address-offset (address)
  (cdr address))

(defun slg19-shift (address amount)
  (cons
   (slg19-address-base address)
   (+ (slg19-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary source
;; functions t_1 and t, together with region, address order, logical
;; strlen, unsigned conversion, linkedness, and constancy.

(defstub slg19-memory-1 (address) t)
(defstub slg19-allocation (index) t)
(defstub slg19-region (base) t)
(defstub slg19-addr-le-op (left right) t)
(defstub slg19-addr-lt-op (left right) t)
(defstub slg19-l-strlen (address) t)
(defstub slg19-to-uint64 (value) t)
(defstub slg19-linked-op () t)
(defstub slg19-sconst-op () t)

;; Preserve all source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk slg19-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (slg19-address-p address)
      (and
       (integerp
        (slg19-memory-1 address))
       (integerp
        (slg19-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (slg19-allocation index)))
     (implies
      (integerp base)
      (integerp
       (slg19-region base)))
     (implies
      (integerp value)
      (integerp
       (slg19-to-uint64 value))))))

(defun slg19-addr-le-p (left right)
  (if (slg19-addr-le-op left right) t nil))

(defun slg19-addr-lt-p (left right)
  (if (slg19-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source relations are exactly integer
;; order on offsets.

(defun-sk slg19-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (slg19-address-p left)
      (slg19-address-p right)
      (equal
       (slg19-address-base left)
       (slg19-address-base right)))
     (and
      (equal
       (slg19-addr-le-p left right)
       (<=
        (slg19-address-offset left)
        (slg19-address-offset right)))
      (equal
       (slg19-addr-lt-p left right)
       (<
        (slg19-address-offset left)
        (slg19-address-offset right)))))))

(defun slg19-linked-p ()
  (if (slg19-linked-op) t nil))

(defun slg19-sconst-p ()
  (if (slg19-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun slg19-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun slg19-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Exact source definition of the C whitespace predicate.

(defun slg19-isspace-p (value)
  (or
   (equal value 9)
   (equal value 10)
   (equal value 12)
   (equal value 13)
   (equal value 32)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk slg19-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (slg19-is-uint64-p
       (slg19-to-uint64 value))
      (implies
       (slg19-is-uint64-p value)
       (equal
        (slg19-to-uint64 value)
        value))
      (equal
       (slg19-to-uint64
        (slg19-to-uint64 value))
       (slg19-to-uint64 value))))))

;; Exact unfoldings of Memory.valid_rw, Memory.invalid, and Memory.included.

(defun slg19-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (slg19-address-base address))
    (<= 0
        (slg19-address-offset address))
    (<=
     (+ (slg19-address-offset address)
        length)
     (slg19-allocation
      (slg19-address-base address))))))

(defun slg19-invalid-p (address length)
  (implies
   (< 0 length)
   (or
    (<=
     (slg19-allocation
      (slg19-address-base address))
     (slg19-address-offset address))
    (<=
     (+ (slg19-address-offset address)
        length)
     0))))

(defun slg19-included-p
    (left left-length right right-length)
  (implies
   (< 0 left-length)
   (and
    (<= 0 right-length)
    (equal
     (slg19-address-base left)
     (slg19-address-base right))
    (<=
     (slg19-address-offset right)
     (slg19-address-offset left))
    (<=
     (+ (slg19-address-offset left)
        left-length)
     (+ (slg19-address-offset right)
        right-length)))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating index remains an
;; internal existential over all mathematical integers, and its character
;; condition remains universal over every mathematical-integer position.

(defun-sk slg19-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (slg19-is-sint8-p
       (slg19-memory-1
        (slg19-shift address position)))))))

(defun-sk slg19-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (slg19-memory-1
       (slg19-shift address index))
      0)
     (slg19-is-uint64-p index)
     (slg19-valid-rw-p
      (slg19-shift address 0)
      (+ 1 index))
     (slg19-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk slg19-strlen-laws-p ()
  (forall (address)
    (implies
     (slg19-address-p address)
     (and
      (if
          (equal
           (slg19-memory-1
            (slg19-shift address 0))
           0)
          (equal
           (slg19-l-strlen address)
           0)
        (equal
         (slg19-to-uint64
          (+ 1
             (slg19-l-strlen
              (slg19-shift address 1))))
         (slg19-l-strlen address)))
      (slg19-is-uint64-p
       (slg19-l-strlen address))))))

;; Preserve the source's two internal universal hypotheses without bounding
;; their integer or address domains.

(defun-sk slg19-no-null-before-p
    (address length)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position length)
       (not
        (equal
         (slg19-memory-1
          (slg19-shift address position))
         0)))))))

(defun-sk slg19-intervening-addresses-space-p
    (lower upper)
  (forall (candidate)
    (implies
     (slg19-address-p candidate)
     (implies
      (slg19-addr-lt-p lower candidate)
      (implies
       (slg19-addr-le-p candidate upper)
       (slg19-isspace-p
        (slg19-memory-1 candidate)))))))

(defun-sk
    ntp4vc-strim-len-assign-exit-part6-goal19-statement ()
  (forall
   (p a a1)
   (implies
    (and
     (booleanp p)
     (slg19-address-p a)
     (slg19-address-p a1)
     (slg19-function-types-p)
     (slg19-address-order-laws-p)
     (slg19-to-uint64-laws-p)
     (slg19-strlen-laws-p))
    (let*
        ((x
          (slg19-l-strlen a))
         (a2
          (slg19-shift a (- x 1)))
         (x1
          (slg19-memory-1 a2))
         (x2
          (slg19-memory-1 a1))
         (a3
          (slg19-shift a -1))
         (a4
          (slg19-shift a1 1)))
      (implies
       (and
        (not (equal x 0))
        (equal
         (slg19-memory-1
          (slg19-shift a x))
         0)
        (not (equal x1 0))
        (< 0 x)
        (<=
         (slg19-region
          (slg19-address-base a))
         0)
        (slg19-linked-p)
        (slg19-sconst-p)
        (slg19-is-sint8-p x2)
        (slg19-valid-string-p a)
        (slg19-is-uint64-p x)
        (slg19-addr-le-p a3 a1)
        (not
         (slg19-invalid-p a4 1))
        (slg19-addr-le-p a1 a2)
        (slg19-is-sint8-p x1)
        (if
            (slg19-addr-le-p a a1)
            (and
             (equal p nil)
             (not
              (slg19-isspace-p x2)))
          (or
            (equal a3 a1)
            (not
             (slg19-isspace-p x2))))
        (slg19-no-null-before-p a x)
        (slg19-intervening-addresses-space-p
         a1 a2))
       (slg19-included-p
        a4
        1
        (slg19-shift a 0)
        (+ 1 x)))))))

(value-triple :itpeval-statement-checked)

:q
