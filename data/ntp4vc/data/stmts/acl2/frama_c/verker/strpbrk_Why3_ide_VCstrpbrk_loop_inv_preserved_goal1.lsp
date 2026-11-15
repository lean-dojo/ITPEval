;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_preserved_goal1:
;; preservation of the strpbrk loop invariant bounding the advanced source
;; address between the second string's start and end, under the stated string,
;; address-order, membership, and quantified no-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spvip1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spvip1-address-base (address)
  (car address))

(defun spvip1-address-offset (address)
  (cdr address))

(defun spvip1-shift (address amount)
  (cons
   (spvip1-address-base address)
   (+ (spvip1-address-offset address)
      amount)))

(defun spvip1-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spvip1-character-memory (address) t)
(defstub spvip1-allocation (index) t)
(defstub spvip1-region (base) t)
(defstub spvip1-addr-le-op (left right) t)
(defstub spvip1-addr-lt-op (left right) t)
(defstub spvip1-l-strlen (address) t)
(defstub spvip1-l-strpbrk (string accept) t)
(defstub spvip1-to-uint64 (value) t)
(defstub spvip1-linked-op () t)
(defstub spvip1-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spvip1-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spvip1-address-p address)
      (and
       (integerp
        (spvip1-character-memory address))
       (integerp
        (spvip1-l-strlen address))))
     (implies
      (and
       (spvip1-address-p address)
       (spvip1-address-p other))
      (spvip1-address-p
       (spvip1-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spvip1-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spvip1-region base)))
     (implies
      (integerp value)
      (integerp
       (spvip1-to-uint64 value))))))

(defun spvip1-addr-le-p (left right)
  (if (spvip1-addr-le-op left right) t nil))

(defun spvip1-addr-lt-p (left right)
  (if (spvip1-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spvip1-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spvip1-address-p left)
      (spvip1-address-p right)
      (equal
       (spvip1-address-base left)
       (spvip1-address-base right)))
     (and
      (equal
       (spvip1-addr-le-p left right)
       (<=
        (spvip1-address-offset left)
        (spvip1-address-offset right)))
      (equal
       (spvip1-addr-lt-p left right)
       (<
        (spvip1-address-offset left)
        (spvip1-address-offset right)))))))

(defun spvip1-linked-p ()
  (if (spvip1-linked-op) t nil))

(defun spvip1-sconst-p ()
  (if (spvip1-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spvip1-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spvip1-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spvip1-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spvip1-is-uint64-p
       (spvip1-to-uint64 value))
      (implies
       (spvip1-is-uint64-p value)
       (equal
        (spvip1-to-uint64 value)
        value))
      (equal
       (spvip1-to-uint64
        (spvip1-to-uint64 value))
       (spvip1-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spvip1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spvip1-address-base address))
    (<= 0
        (spvip1-address-offset address))
    (<=
     (+ (spvip1-address-offset address)
        length)
     (spvip1-allocation
      (spvip1-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spvip1-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spvip1-is-sint8-p
       (spvip1-character-memory
        (spvip1-shift address position)))))))

(defun-sk spvip1-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spvip1-character-memory
       (spvip1-shift address index))
      0)
     (spvip1-is-uint64-p index)
     (spvip1-valid-rw-p
      (spvip1-shift address 0)
      (+ 1 index))
     (spvip1-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spvip1-strlen-laws-p ()
  (forall (address)
    (implies
     (spvip1-address-p address)
     (and
      (if
          (equal
           (spvip1-character-memory
            (spvip1-shift address 0))
           0)
          (equal
           (spvip1-l-strlen address)
           0)
        (equal
         (spvip1-to-uint64
          (+ 1
             (spvip1-l-strlen
              (spvip1-shift address 1))))
         (spvip1-l-strlen address)))
      (spvip1-is-uint64-p
       (spvip1-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spvip1-in-array-p (start value)
  (exists (candidate)
    (and
     (spvip1-address-p candidate)
     (equal
      (spvip1-character-memory candidate)
      value)
     (spvip1-addr-le-p start candidate)
     (spvip1-addr-lt-p
      candidate
      (spvip1-shift
       start
       (spvip1-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spvip1-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spvip1-address-p string)
      (spvip1-address-p accept))
     (and
      (implies
       (equal
        (spvip1-character-memory string)
        0)
       (equal
        (spvip1-l-strpbrk string accept)
        (spvip1-null-address)))
      (implies
       (and
        (not
         (equal
          (spvip1-character-memory string)
          0))
        (spvip1-in-array-p
         accept
         (spvip1-character-memory string)))
       (equal
        (spvip1-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spvip1-character-memory string)
          0))
        (not
         (spvip1-in-array-p
          accept
          (spvip1-character-memory string))))
       (equal
        (spvip1-l-strpbrk
         (spvip1-shift string 1)
         accept)
        (spvip1-l-strpbrk string accept)))))))

;; The source's four quantified no-match hypotheses remain universal over
;; every address rather than being replaced by external witnesses.

(defun-sk spvip1-no-x-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spvip1-address-p candidate)
     (implies
      (spvip1-addr-lt-p candidate current)
      (implies
       (spvip1-addr-le-p start candidate)
       (not
        (equal
         value
         (spvip1-character-memory candidate))))))))

(defun-sk spvip1-no-x-before-end-p
    (start end value)
  (forall (candidate)
    (implies
     (spvip1-address-p candidate)
     (implies
      (spvip1-addr-le-p start candidate)
      (implies
       (spvip1-addr-lt-p candidate end)
       (not
        (equal
         value
         (spvip1-character-memory candidate))))))))

(defun-sk spvip1-cross-values-distinct-before-p
    (first-start first-current second-start second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvip1-address-p first-candidate)
      (spvip1-address-p second-candidate))
     (implies
      (spvip1-addr-lt-p first-candidate first-current)
      (implies
       (spvip1-addr-le-p second-start second-candidate)
       (implies
        (spvip1-addr-le-p first-start first-candidate)
        (implies
         (spvip1-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvip1-character-memory first-candidate)
           (spvip1-character-memory second-candidate))))))))))

(defun-sk spvip1-cross-values-distinct-through-p
    (first-start first-current second-start second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvip1-address-p first-candidate)
      (spvip1-address-p second-candidate))
     (implies
      (spvip1-addr-le-p first-candidate first-current)
      (implies
       (spvip1-addr-le-p second-start second-candidate)
       (implies
        (spvip1-addr-le-p first-start first-candidate)
        (implies
         (spvip1-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvip1-character-memory first-candidate)
           (spvip1-character-memory second-candidate))))))))))

(defun-sk
    ntp4vc-strpbrk-loop-inv-preserved-goal1-statement ()
  (forall
   (a1 a2 a3 a)
   (implies
    (and
     (spvip1-address-p a1)
     (spvip1-address-p a2)
     (spvip1-address-p a3)
     (spvip1-address-p a)
     (spvip1-function-types-p)
     (spvip1-address-order-laws-p)
     (spvip1-to-uint64-laws-p)
     (spvip1-strlen-laws-p)
     (spvip1-strpbrk-laws-p))
    (let*
        ((x
          (spvip1-character-memory a1))
         (a4
          (spvip1-shift
           a2
           (spvip1-l-strlen a2)))
         (a5
          (spvip1-shift
           a3
           (spvip1-l-strlen a3)))
         (a6
          (spvip1-shift a1 1)))
      (implies
       (and
        (equal
         (spvip1-character-memory a)
         0)
        (not (equal x 0))
        (equal
         (spvip1-l-strpbrk a3 a2)
         (spvip1-l-strpbrk a1 a2))
        (<=
         (spvip1-region
          (spvip1-address-base a2))
         0)
        (<=
         (spvip1-region
          (spvip1-address-base a3))
         0)
        (spvip1-linked-p)
        (spvip1-sconst-p)
        (spvip1-addr-le-p a2 a)
        (spvip1-addr-le-p a3 a1)
        (spvip1-is-sint8-p x)
        (spvip1-valid-string-p a)
        (spvip1-valid-string-p a1)
        (spvip1-valid-string-p a2)
        (spvip1-valid-string-p a3)
        (spvip1-addr-le-p a a4)
        (spvip1-addr-le-p a1 a5)
        (implies
         (spvip1-in-array-p a2 x)
         (spvip1-in-array-p a x))
        (spvip1-no-x-before-current-p
         a2 a x)
        (spvip1-no-x-before-end-p
         a2 a4 x)
        (spvip1-cross-values-distinct-before-p
         a3 a1 a2 a4)
        (spvip1-cross-values-distinct-through-p
         a3 a1 a2 a4))
       (and
        (spvip1-addr-le-p a3 a6)
        (spvip1-addr-le-p a6 a5)))))))

(value-triple :itpeval-statement-checked)

:q
