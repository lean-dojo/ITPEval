;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_term_positive_goal17:
;; the current first-string offset is at most its start offset plus its
;; logical length, under the stated strpbrk, valid-string, address-order,
;; membership, and quantified no-match hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spg17-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spg17-address-base (address)
  (car address))

(defun spg17-address-offset (address)
  (cdr address))

(defun spg17-shift (address amount)
  (cons
   (spg17-address-base address)
   (+ (spg17-address-offset address)
      amount)))

(defun spg17-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spg17-character-memory (address) t)
(defstub spg17-allocation (index) t)
(defstub spg17-region (base) t)
(defstub spg17-addr-le-op (left right) t)
(defstub spg17-addr-lt-op (left right) t)
(defstub spg17-l-strlen (address) t)
(defstub spg17-l-strpbrk (string accept) t)
(defstub spg17-to-uint64 (value) t)
(defstub spg17-linked-op () t)
(defstub spg17-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spg17-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spg17-address-p address)
      (and
       (integerp
        (spg17-character-memory address))
       (integerp
        (spg17-l-strlen address))))
     (implies
      (and
       (spg17-address-p address)
       (spg17-address-p other))
      (spg17-address-p
       (spg17-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spg17-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spg17-region base)))
     (implies
      (integerp value)
      (integerp
       (spg17-to-uint64 value))))))

(defun spg17-addr-le-p (left right)
  (if (spg17-addr-le-op left right) t nil))

(defun spg17-addr-lt-p (left right)
  (if (spg17-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spg17-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spg17-address-p left)
      (spg17-address-p right)
      (equal
       (spg17-address-base left)
       (spg17-address-base right)))
     (and
      (equal
       (spg17-addr-le-p left right)
       (<=
        (spg17-address-offset left)
        (spg17-address-offset right)))
      (equal
       (spg17-addr-lt-p left right)
       (<
        (spg17-address-offset left)
        (spg17-address-offset right)))))))

(defun spg17-linked-p ()
  (if (spg17-linked-op) t nil))

(defun spg17-sconst-p ()
  (if (spg17-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spg17-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spg17-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spg17-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg17-is-uint64-p
       (spg17-to-uint64 value))
      (implies
       (spg17-is-uint64-p value)
       (equal
        (spg17-to-uint64 value)
        value))
      (equal
       (spg17-to-uint64
        (spg17-to-uint64 value))
       (spg17-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spg17-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spg17-address-base address))
    (<= 0
        (spg17-address-offset address))
    (<=
     (+ (spg17-address-offset address)
        length)
     (spg17-allocation
      (spg17-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spg17-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spg17-is-sint8-p
       (spg17-character-memory
        (spg17-shift address position)))))))

(defun-sk spg17-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spg17-character-memory
       (spg17-shift address index))
      0)
     (spg17-is-uint64-p index)
     (spg17-valid-rw-p
      (spg17-shift address 0)
      (+ 1 index))
     (spg17-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spg17-strlen-laws-p ()
  (forall (address)
    (implies
     (spg17-address-p address)
     (and
      (if
          (equal
           (spg17-character-memory
            (spg17-shift address 0))
           0)
          (equal
           (spg17-l-strlen address)
           0)
        (equal
         (spg17-to-uint64
          (+ 1
             (spg17-l-strlen
              (spg17-shift address 1))))
         (spg17-l-strlen address)))
      (spg17-is-uint64-p
       (spg17-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spg17-in-array-p (start value)
  (exists (candidate)
    (and
     (spg17-address-p candidate)
     (equal
      (spg17-character-memory candidate)
      value)
     (spg17-addr-le-p start candidate)
     (spg17-addr-lt-p
      candidate
      (spg17-shift
       start
       (spg17-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spg17-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spg17-address-p string)
      (spg17-address-p accept))
     (and
      (implies
       (equal
        (spg17-character-memory string)
        0)
       (equal
        (spg17-l-strpbrk string accept)
        (spg17-null-address)))
      (implies
       (and
        (not
         (equal
          (spg17-character-memory string)
          0))
        (spg17-in-array-p
         accept
         (spg17-character-memory string)))
       (equal
        (spg17-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spg17-character-memory string)
          0))
        (not
         (spg17-in-array-p
          accept
          (spg17-character-memory string))))
       (equal
        (spg17-l-strpbrk
         (spg17-shift string 1)
         accept)
        (spg17-l-strpbrk string accept)))))))

;; The source's four quantified no-match hypotheses remain universal over
;; every address rather than being replaced by external witnesses.

(defun-sk spg17-no-x-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spg17-address-p candidate)
     (implies
      (spg17-addr-lt-p candidate current)
      (implies
       (spg17-addr-le-p start candidate)
       (not
        (equal
         value
         (spg17-character-memory candidate))))))))

(defun-sk spg17-no-x-before-end-p
    (start end value)
  (forall (candidate)
    (implies
     (spg17-address-p candidate)
     (implies
      (spg17-addr-le-p start candidate)
      (implies
       (spg17-addr-lt-p candidate end)
       (not
        (equal
         value
         (spg17-character-memory candidate))))))))

(defun-sk spg17-cross-values-before-current-distinct-p
    (second-start first-start first-current second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spg17-address-p first-candidate)
      (spg17-address-p second-candidate))
     (implies
      (spg17-addr-lt-p first-candidate first-current)
      (implies
       (spg17-addr-le-p second-start second-candidate)
       (implies
        (spg17-addr-le-p first-start first-candidate)
        (implies
         (spg17-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spg17-character-memory first-candidate)
           (spg17-character-memory second-candidate))))))))))

(defun-sk spg17-cross-values-through-current-distinct-p
    (second-start first-start first-current second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spg17-address-p first-candidate)
      (spg17-address-p second-candidate))
     (implies
      (spg17-addr-le-p first-candidate first-current)
      (implies
       (spg17-addr-le-p second-start second-candidate)
       (implies
        (spg17-addr-le-p first-start first-candidate)
        (implies
         (spg17-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spg17-character-memory first-candidate)
           (spg17-character-memory second-candidate))))))))))

(defun-sk
    ntp4vc-strpbrk-loop-term-positive-goal17-statement
    ()
  (forall
   (a a1 a2 a3)
   (implies
    (and
     (spg17-address-p a)
     (spg17-address-p a1)
     (spg17-address-p a2)
     (spg17-address-p a3)
     (spg17-function-types-p)
     (spg17-address-order-laws-p)
     (spg17-to-uint64-laws-p)
     (spg17-strlen-laws-p)
     (spg17-strpbrk-laws-p))
    (let*
        ((x
          (spg17-character-memory a1))
         (a4
          (spg17-shift
           a2
           (spg17-l-strlen a2)))
         (x1
          (spg17-l-strlen a3)))
      (implies
       (and
        (equal
         (spg17-character-memory a)
         0)
        (not (equal x 0))
        (equal
         (spg17-l-strpbrk a3 a2)
         (spg17-l-strpbrk a1 a2))
        (<=
         (spg17-region
          (spg17-address-base a2))
         0)
        (<=
         (spg17-region
          (spg17-address-base a3))
         0)
        (spg17-linked-p)
        (spg17-sconst-p)
        (spg17-addr-le-p a2 a)
        (spg17-addr-le-p a3 a1)
        (spg17-is-sint8-p x)
        (spg17-valid-string-p a)
        (spg17-valid-string-p a1)
        (spg17-valid-string-p a2)
        (spg17-valid-string-p a3)
        (spg17-addr-le-p a a4)
        (spg17-addr-le-p
         a1
         (spg17-shift a3 x1))
        (implies
         (spg17-in-array-p a2 x)
         (spg17-in-array-p a x))
        (spg17-no-x-before-current-p
         a2 a x)
        (spg17-no-x-before-end-p
         a2 a4 x)
        (spg17-cross-values-before-current-distinct-p
         a2 a3 a1 a4)
        (spg17-cross-values-through-current-distinct-p
         a2 a3 a1 a4))
       (<=
        (spg17-address-offset a1)
        (+ (spg17-address-offset a3)
           x1)))))))

(value-triple :itpeval-statement-checked)

:q
