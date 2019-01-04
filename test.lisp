; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
#|(defmacro lenp (delta n)
  (and (natp n) (listp delta) (>= (len delta) n))
  )|#

(defun tao-listp (tl)
  (cond ((integerp tl) T)
        ((equal tl nil) T)
        ((true-listp tl) (and (tao-listp (first tl)) (tao-listp (rest tl))))
        )
  )

#|(defmacro tao-listp (tl)
  (list 'cond (list (list 'integerp tl) T)
              (list (list 'endp tl) T)
              (list (list 'listp tl) (list 'and (list 'tao-listp (list 'first tl)) (list 'tao-listp (list 'rest tl))))))|#

#|(defunc tao-listp (tl)
  :input-contract (or (integerp tl) (endp tl) (consp tl))
  :output-contract (boolean p (tao-listp tl))
  (cond ((integerp tl) T)
        ((endp tl) T)
        ((consp tl) (and (tao-listp (first tl)) (tao-listp (second tl))))
        )
  )|#

(defmacro lenp (delta n)
  (list 'and (list 'natp n) (list 'true-listp delta) (list '>= (list 'len delta) n))
  )

#|(defunc lenp_check (delta n)
  :input-contract (and (tao-listp delta) (natp n) (>= (len delta) n))
  :output-contract (booleanp (lenp_check delta n))
  (lenp delta n)
  )|#

(defunc i_return (delta)
   :input-contract (and (listp delta) (integerp (first delta)))
   :output-contract (integerp (first delta))
   (first delta)
   )

(defunc taop (a)
  :input-contract a
  :output-contract (booleanp (taop a))
  (or (natp a) (listp a))
  )


(defunc i_dup (delta)
  :input-contract (listp delta)
  :output-contract (listp (i_dup delta))
  (cons (first delta) delta)
  )

(defunc i_const (n delta)
  :input-contract (listp delta)
  :output-contract (listp (i_const n delta))
  (cons n delta)
  )

(defmacro if_zero (delta a f1 f2)
  (list (if (equal a 0) f1 f2) delta)
  )


(defmacro goto (delta f)
  (list f delta)
  )

(defunc i_pop (delta)
  :input-contract (and (true-listp delta) (lenp delta 1))
  :output-contract (true-listp (i_pop delta))
  (rest delta)
  )

(defunc i_add (delta)
  :input-contract (and (lenp delta 2) (integerp (first delta)) (integerp (second delta)))
  :output-contract (and (true-listp (i_add delta)) (integerp (first (i_add delta))))
  (cons (+ (first delta) (second delta)) (i_pop (i_pop delta)))
  )

(defunc i_swap (delta)
  :input-contract (lenp delta 2)
  :output-contract (listp (i_swap delta))
  (cons (second delta) (cons (first delta) (rest (rest delta))))
  )

(defthm nil-if-pop-twice-from-list-of-two
  (implies (and (true-listp x) (equal (len x) 2)) (equal (i_pop (i_pop x)) nil))
  )

(defunc i_mul (delta)
  :input-contract (and 
                   (true-listp delta) 
                   (lenp delta 2) 
                   (integerp (first delta)) 
                   (integerp (second delta))
                   )
  :output-contract (and
                    (true-listp (i_mul delta))
                    (integerp (first (i_mul delta))))
  :function-contract-hints (nil-if-pop-twice-from-list-of-two)
  (cons (* (first delta) (second delta)) (i_pop (i_pop delta)))
  )

(defunc i_div (delta)
  :input-contract (and 
                   (true-listp delta) 
                   (lenp delta 2) 
                   (integerp (first delta)) 
                   (integerp (second delta))
                   (/= (second delta) 0)
                   )
  :output-contract (and
                    (true-listp (i_div delta))
                    (integerp (first (i_div delta))))
  (cons (floor (/ (first delta) (second delta)) 1) (i_pop (i_pop delta)))
  )

(defunc i_mod (delta)
  :input-contract (and 
                   (true-listp delta) 
                   (lenp delta 2) 
                   (integerp (first delta)) 
                   (integerp (second delta))
                   (/= (second delta) 0)
                   )
  :output-contract (and
                    (true-listp (i_mod delta))
                    (integerp (first (i_mod delta))))
  (cons (mod (first delta) (second delta)) (i_pop (i_pop delta)))
  )#|ACL2s-ToDo-Line|#


#|*********************************************************************|#

