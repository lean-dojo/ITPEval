;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_7_preserved_goal10:
;; preservation of the strpbrk loop invariant that a selected accept address
;; contains a byte distinct from the current source byte, under the stated
;; string, address-order, membership, and quantified no-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spvi7p10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spvi7p10-address-base (address)
  (car address))

(defun spvi7p10-address-offset (address)
  (cdr address))

(defun spvi7p10-shift (address amount)
  (cons
   (spvi7p10-address-base address)
   (+ (spvi7p10-address-offset address)
      amount)))

(defun spvi7p10-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spvi7p10-character-memory (address) t)
(defstub spvi7p10-allocation (index) t)
(defstub spvi7p10-region (base) t)
(defstub spvi7p10-addr-le-op (left right) t)
(defstub spvi7p10-addr-lt-op (left right) t)
(defstub spvi7p10-l-strlen (address) t)
(defstub spvi7p10-l-strpbrk (string accept) t)
(defstub spvi7p10-to-uint64 (value) t)
(defstub spvi7p10-linked-op () t)
(defstub spvi7p10-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spvi7p10-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spvi7p10-address-p address)
      (and
       (integerp
        (spvi7p10-character-memory address))
       (integerp
        (spvi7p10-l-strlen address))))
     (implies
      (and
       (spvi7p10-address-p address)
       (spvi7p10-address-p other))
      (spvi7p10-address-p
       (spvi7p10-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spvi7p10-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spvi7p10-region base)))
     (implies
      (integerp value)
      (integerp
       (spvi7p10-to-uint64 value))))))

(defun spvi7p10-addr-le-p (left right)
  (if (spvi7p10-addr-le-op left right) t nil))

(defun spvi7p10-addr-lt-p (left right)
  (if (spvi7p10-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spvi7p10-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spvi7p10-address-p left)
      (spvi7p10-address-p right)
      (equal
       (spvi7p10-address-base left)
       (spvi7p10-address-base right)))
     (and
      (equal
       (spvi7p10-addr-le-p left right)
       (<=
        (spvi7p10-address-offset left)
        (spvi7p10-address-offset right)))
      (equal
       (spvi7p10-addr-lt-p left right)
       (<
        (spvi7p10-address-offset left)
        (spvi7p10-address-offset right)))))))

(defun spvi7p10-linked-p ()
  (if (spvi7p10-linked-op) t nil))

(defun spvi7p10-sconst-p ()
  (if (spvi7p10-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spvi7p10-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spvi7p10-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spvi7p10-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spvi7p10-is-uint64-p
       (spvi7p10-to-uint64 value))
      (implies
       (spvi7p10-is-uint64-p value)
       (equal
        (spvi7p10-to-uint64 value)
        value))
      (equal
       (spvi7p10-to-uint64
        (spvi7p10-to-uint64 value))
       (spvi7p10-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spvi7p10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spvi7p10-address-base address))
    (<= 0
        (spvi7p10-address-offset address))
    (<=
     (+ (spvi7p10-address-offset address)
        length)
     (spvi7p10-allocation
      (spvi7p10-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spvi7p10-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spvi7p10-is-sint8-p
       (spvi7p10-character-memory
        (spvi7p10-shift address position)))))))

(defun-sk spvi7p10-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spvi7p10-character-memory
       (spvi7p10-shift address index))
      0)
     (spvi7p10-is-uint64-p index)
     (spvi7p10-valid-rw-p
      (spvi7p10-shift address 0)
      (+ 1 index))
     (spvi7p10-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spvi7p10-strlen-laws-p ()
  (forall (address)
    (implies
     (spvi7p10-address-p address)
     (and
      (if
          (equal
           (spvi7p10-character-memory
            (spvi7p10-shift address 0))
           0)
          (equal
           (spvi7p10-l-strlen address)
           0)
        (equal
         (spvi7p10-to-uint64
          (+ 1
             (spvi7p10-l-strlen
              (spvi7p10-shift address 1))))
         (spvi7p10-l-strlen address)))
      (spvi7p10-is-uint64-p
       (spvi7p10-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spvi7p10-in-array-p (start value)
  (exists (candidate)
    (and
     (spvi7p10-address-p candidate)
     (equal
      (spvi7p10-character-memory candidate)
      value)
     (spvi7p10-addr-le-p start candidate)
     (spvi7p10-addr-lt-p
      candidate
      (spvi7p10-shift
       start
       (spvi7p10-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spvi7p10-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spvi7p10-address-p string)
      (spvi7p10-address-p accept))
     (and
      (implies
       (equal
        (spvi7p10-character-memory string)
        0)
       (equal
        (spvi7p10-l-strpbrk string accept)
        (spvi7p10-null-address)))
      (implies
       (and
        (not
         (equal
          (spvi7p10-character-memory string)
          0))
        (spvi7p10-in-array-p
         accept
         (spvi7p10-character-memory string)))
       (equal
        (spvi7p10-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spvi7p10-character-memory string)
          0))
        (not
         (spvi7p10-in-array-p
          accept
          (spvi7p10-character-memory string))))
       (equal
        (spvi7p10-l-strpbrk
         (spvi7p10-shift string 1)
         accept)
        (spvi7p10-l-strpbrk string accept)))))))

;; The source's two quantified no-match hypotheses remain universal over
;; every address rather than being replaced by external witnesses.

(defun-sk spvi7p10-no-value-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spvi7p10-address-p candidate)
     (implies
      (spvi7p10-addr-lt-p candidate current)
      (implies
       (spvi7p10-addr-le-p start candidate)
       (not
        (equal
         value
         (spvi7p10-character-memory candidate))))))))

(defun-sk spvi7p10-cross-values-distinct-p
    (first-start first-current second-start second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvi7p10-address-p first-candidate)
      (spvi7p10-address-p second-candidate))
     (implies
      (spvi7p10-addr-lt-p first-candidate first-current)
      (implies
       (spvi7p10-addr-le-p second-start second-candidate)
       (implies
        (spvi7p10-addr-le-p first-start first-candidate)
        (implies
         (spvi7p10-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvi7p10-character-memory first-candidate)
           (spvi7p10-character-memory second-candidate))))))))))

(defun-sk
    ntp4vc-strpbrk-loop-inv-7-preserved-goal10-statement ()
  (forall
   (a a1 a2 a3 a4)
   (implies
    (and
     (spvi7p10-address-p a)
     (spvi7p10-address-p a1)
     (spvi7p10-address-p a2)
     (spvi7p10-address-p a3)
     (spvi7p10-address-p a4)
     (spvi7p10-function-types-p)
     (spvi7p10-address-order-laws-p)
     (spvi7p10-to-uint64-laws-p)
     (spvi7p10-strlen-laws-p)
     (spvi7p10-strpbrk-laws-p))
    (let*
        ((x
          (spvi7p10-character-memory a))
         (x1
          (spvi7p10-character-memory a1))
         (a5
          (spvi7p10-shift
           a2
           (spvi7p10-l-strlen a2))))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (not (equal x1 x))
        (equal
         (spvi7p10-l-strpbrk a3 a2)
         (spvi7p10-l-strpbrk a1 a2))
        (<=
         (spvi7p10-region
          (spvi7p10-address-base a2))
         0)
        (<=
         (spvi7p10-region
          (spvi7p10-address-base a3))
         0)
        (spvi7p10-linked-p)
        (spvi7p10-sconst-p)
        (spvi7p10-addr-le-p a2 a)
        (spvi7p10-addr-le-p a2 a4)
        (spvi7p10-addr-le-p a3 a1)
        (spvi7p10-is-sint8-p x)
        (spvi7p10-is-sint8-p x1)
        (spvi7p10-valid-string-p a)
        (spvi7p10-valid-string-p a1)
        (spvi7p10-valid-string-p a2)
        (spvi7p10-valid-string-p a3)
        (spvi7p10-addr-lt-p
         a4
         (spvi7p10-shift a 1))
        (spvi7p10-addr-le-p a a5)
        (spvi7p10-addr-le-p
         a1
         (spvi7p10-shift
          a3
          (spvi7p10-l-strlen a3)))
        (implies
         (spvi7p10-in-array-p a2 x1)
         (spvi7p10-in-array-p a x1))
        (spvi7p10-no-value-before-current-p
         a2 a x1)
        (spvi7p10-cross-values-distinct-p
         a3 a1 a2 a5))
       (not
        (equal
         (spvi7p10-character-memory a4)
         x1)))))))

(value-triple :itpeval-statement-checked)

:q
