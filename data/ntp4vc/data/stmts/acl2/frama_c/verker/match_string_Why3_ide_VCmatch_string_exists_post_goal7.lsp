;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/match_string_Why3_ide_VCmatch_string_exists_post_goal7:
;; equality of the match-string result with the loop result under the source
;; memory, string-validity, framing, comparison, and prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ms7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ms7-address-base (address)
  (car address))

(defun ms7-address-offset (address)
  (cdr address))

(defun ms7-shift (address amount)
  (cons
   (ms7-address-base address)
   (+ (ms7-address-offset address) amount)))

(defun ms7-null-address ()
  (cons 0 0))

;; Conservative interfaces for the arbitrary pointer memory t_2, character
;; memory t_1, allocation map t, region function, and source logical string
;; operations and predicates.

(defstub ms7-pointer-memory (address) t)
(defstub ms7-character-memory (address) t)
(defstub ms7-allocation (index) t)
(defstub ms7-region (base) t)
(defstub ms7-l-strncmp (left right count) t)
(defstub ms7-l-strlen (address) t)
(defstub ms7-l-real-len (address count) t)
(defstub ms7-l-match-string (address count target) t)
(defstub ms7-to-uint8 (value) t)
(defstub ms7-to-sint8 (value) t)
(defstub ms7-to-uint64 (value) t)
(defstub ms7-to-sint64 (value) t)
(defstub ms7-linked-op () t)
(defstub ms7-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; integer domains.

(defun-sk ms7-function-types-p ()
  (forall (address index base left right count target)
    (and
     (implies
      (ms7-address-p address)
      (and
       (ms7-address-p (ms7-pointer-memory address))
       (integerp (ms7-character-memory address))
       (integerp (ms7-l-strlen address))))
     (implies
      (integerp index)
      (integerp (ms7-allocation index)))
     (implies
      (integerp base)
      (integerp (ms7-region base)))
     (implies
      (and
       (ms7-address-p left)
       (ms7-address-p right)
       (integerp count))
      (integerp (ms7-l-strncmp left right count)))
     (implies
      (and
       (ms7-address-p address)
       (integerp count))
      (integerp (ms7-l-real-len address count)))
     (implies
      (and
       (ms7-address-p address)
       (integerp count)
       (ms7-address-p target))
      (integerp
       (ms7-l-match-string address count target))))))

(defun ms7-linked-p ()
  (if (ms7-linked-op) t nil))

(defun ms7-sconst-p ()
  (if (ms7-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun ms7-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun ms7-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun ms7-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun ms7-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun ms7-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions.

(defun-sk ms7-to-uint-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ms7-is-uint8-p
       (ms7-to-uint8 value))
      (ms7-is-uint64-p
       (ms7-to-uint64 value))
      (implies
       (ms7-is-uint8-p value)
       (equal
        (ms7-to-uint8 value)
        value))
      (implies
       (ms7-is-uint64-p value)
       (equal
        (ms7-to-uint64 value)
        value))
      (equal
       (ms7-to-uint8
        (ms7-to-uint8 value))
       (ms7-to-uint8 value))
      (equal
       (ms7-to-uint64
        (ms7-to-uint64 value))
       (ms7-to-uint64 value))))))

(defun-sk ms7-to-sint-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ms7-is-sint8-p
       (ms7-to-sint8 value))
      (ms7-is-sint64-p
       (ms7-to-sint64 value))
      (implies
       (ms7-is-sint8-p value)
       (equal
        (ms7-to-sint8 value)
        value))
      (implies
       (ms7-is-sint64-p value)
       (equal
        (ms7-to-sint64 value)
        value))
      (equal
       (ms7-to-sint8
        (ms7-to-sint8 value))
       (ms7-to-sint8 value))
      (equal
       (ms7-to-sint64
        (ms7-to-sint64 value))
       (ms7-to-sint64 value))))))

;; Exact proj_int8 and proj_int64 interactions from the source context.

(defun-sk ms7-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (ms7-to-sint8
        (ms7-to-uint8 value))
       (ms7-to-sint8 value))
      (equal
       (ms7-to-sint64
        (ms7-to-uint64 value))
       (ms7-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the fixed allocation map t.

(defun ms7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ms7-address-base address))
    (<= 0 (ms7-address-offset address))
    (<=
     (+ (ms7-address-offset address) length)
     (ms7-allocation (ms7-address-base address))))))

;; Exact unfolding of Memory.framed for the pointer memory t_2.

(defun-sk ms7-framed-p ()
  (forall (address)
    (implies
     (ms7-address-p address)
     (<=
      (ms7-region
       (ms7-address-base
        (ms7-pointer-memory address)))
      0))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating index remains an
;; internal existential over all mathematical integers.

(defun-sk ms7-string-chars-sint8-through-p (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (ms7-is-sint8-p
       (ms7-character-memory
        (ms7-shift address position)))))))

(defun-sk ms7-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (ms7-character-memory
       (ms7-shift address index))
      0)
     (ms7-is-uint64-p index)
     (ms7-valid-rw-p
      (ms7-shift address 0)
      (+ 1 index))
     (ms7-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk ms7-strlen-laws-p ()
  (forall (address)
    (implies
     (ms7-address-p address)
     (and
      (if
          (equal
           (ms7-character-memory
            (ms7-shift address 0))
           0)
          (equal (ms7-l-strlen address) 0)
        (equal
         (ms7-to-uint64
          (+ 1
             (ms7-l-strlen
              (ms7-shift address 1))))
         (ms7-l-strlen address)))
      (ms7-is-uint64-p
       (ms7-l-strlen address))))))

;; A_StrCmp.l_cmp and l_strcmp, with the universal closure of the source
;; fixpoint equation for l_strncmp_1'.

(defun ms7-l-cmp (left right)
  (if (equal right left)
      0
    (if (< left right)
        -1
      1)))

(defun ms7-l-strcmp (left right)
  (ms7-l-strncmp
   left
   right
   (ms7-l-strlen left)))

(defun-sk ms7-strncmp-law-p ()
  (forall (left right count)
    (implies
     (and
      (ms7-address-p left)
      (ms7-address-p right)
      (integerp count))
     (if
         (equal count -1)
         (equal
          (ms7-l-strncmp left right count)
          0)
       (if
           (equal
            (ms7-character-memory
             (ms7-shift right 0))
            (ms7-character-memory
             (ms7-shift left 0)))
           (equal
            (ms7-l-strncmp
             (ms7-shift left 1)
             (ms7-shift right 1)
             (- count 1))
            (ms7-l-strncmp left right count))
         (equal
          (ms7-l-cmp
           (ms7-to-uint8
            (ms7-character-memory
             (ms7-shift left 0)))
           (ms7-to-uint8
            (ms7-character-memory
             (ms7-shift right 0))))
          (ms7-l-strncmp left right count)))))))

;; Universal closures of A_MatchString.fix_l_real_len and Q_TL_real_len.

(defun-sk ms7-real-len-laws-p ()
  (forall (address count)
    (implies
     (and
      (ms7-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (ms7-pointer-memory
             (ms7-shift address 0))
            (ms7-null-address)))
          (equal
           (ms7-l-real-len address count)
           0)
        (equal
         (ms7-to-uint64
          (+ 1
             (ms7-l-real-len
              (ms7-shift address 1)
              (ms7-to-uint64 (- count 1)))))
         (ms7-l-real-len address count)))
      (ms7-is-uint64-p
       (ms7-l-real-len address count))))))

;; Universal closures of A_MatchString.fix_l_match_string and
;; Q_TL_match_string.

(defun-sk ms7-match-string-laws-p ()
  (forall (address count target)
    (implies
     (and
      (ms7-address-p address)
      (integerp count)
      (ms7-address-p target))
     (and
      (if
          (equal count 0)
          (equal
           (ms7-l-match-string address count target)
           0)
        (if
            (equal
             (ms7-l-strcmp
              (ms7-pointer-memory
               (ms7-shift address 0))
              target)
             0)
            (equal
             (ms7-l-match-string address count target)
             0)
          (equal
           (ms7-l-match-string
            (ms7-shift address 1)
            (ms7-to-uint64 (- count 1))
            target)
           (ms7-l-match-string address count target))))
      (ms7-is-uint64-p
       (ms7-l-match-string address count target))))))

;; The source's four quantified loop and string-equality hypotheses retain
;; their internal universal scope.

(defun-sk ms7-prior-strings-valid-p (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (ms7-valid-string-p
        (ms7-pointer-memory
         (ms7-shift a1 index))))))))

(defun-sk ms7-prior-comparisons-nonzero-p (a1 right bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (not
        (equal
         (ms7-l-strcmp
          (ms7-pointer-memory
           (ms7-shift a1 index))
          right)
         0)))))))

(defun-sk ms7-real-prefix-strings-valid-p (a1 bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index bound)
       (implies
        (ms7-is-uint64-p index)
        (ms7-valid-string-p
         (ms7-pointer-memory
          (ms7-shift a1 index)))))))))

(defun-sk ms7-strings-equal-or-outside-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (or
      (equal
       (ms7-character-memory
        (ms7-shift left index))
       (ms7-character-memory
        (ms7-shift right index)))
      (< index 0)
      (< (ms7-l-strlen left) index)))))

(defun-sk ntp4vc-match-string-exists-post-goal7-statement ()
  (forall
   (a1 i i1 i3 a i2)
   (implies
    (and
     (ms7-address-p a1)
     (integerp i)
     (integerp i1)
     (integerp i3)
     (ms7-address-p a)
     (integerp i2)
     (ms7-function-types-p)
     (ms7-to-uint-laws-p)
     (ms7-to-sint-laws-p)
     (ms7-signed-unsigned-projection-laws-p)
     (ms7-strlen-laws-p)
     (ms7-strncmp-law-p)
     (ms7-real-len-laws-p)
     (ms7-match-string-laws-p))
    (let*
        ((x
          (ms7-l-real-len a1 i))
         (a2
          (ms7-pointer-memory
           (ms7-shift a1 i1)))
         (a3
          (ms7-shift a1 0)))
      (implies
       (and
        (equal
         (ms7-l-strcmp
          (ms7-pointer-memory
           (ms7-shift a1 i3))
          a)
         0)
        (<= 0 i2)
        (<= 0 i3)
        (<= (ms7-region (ms7-address-base a)) 0)
        (<= (ms7-region (ms7-address-base a1)) 0)
        (<= x i)
        (< i3 x)
        (<= i2 x)
        (<= i 2147483647)
        (ms7-framed-p)
        (ms7-linked-p)
        (ms7-sconst-p)
        (ms7-is-sint32-p i2)
        (ms7-is-uint64-p i)
        (ms7-is-uint64-p i3)
        (ms7-valid-string-p a)
        (if
            (< (ms7-to-uint64 i2) i)
            (if
                (equal
                 (ms7-pointer-memory
                  (ms7-shift a1 i2))
                 (ms7-null-address))
                (equal i1 -22)
              (and
               (equal i2 i1)
               (equal (ms7-l-strcmp a2 a) 0)
               (ms7-valid-string-p a2)
               (ms7-strings-equal-or-outside-p a2 a)))
          (equal i1 -22))
        (implies
         (equal x i)
         (ms7-valid-rw-p a3 i))
        (implies
         (< x i)
         (ms7-valid-rw-p a3 (+ 1 x)))
        (ms7-prior-strings-valid-p a1 i2)
        (ms7-prior-comparisons-nonzero-p a1 a i2)
        (ms7-real-prefix-strings-valid-p a1 x))
       (equal
        (ms7-l-match-string a1 x a)
        i1))))))

(value-triple :itpeval-statement-checked)

:q
