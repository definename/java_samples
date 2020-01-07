public class Person {

private /*@ spec_public non_null @*/ String name;
private /*@ spec_public @*/ int weight;

/*@ public invariant !name.equals("")
@	&& weight >= 0;
@*/

/*@ also
@	ensures \result != null
@	&& (* \result is a displayable
@	form of this person *);
@*/
public String toString() {
    return "Person(\"" + name + "\"," + weight + ")";
}

//@ also
//@ ensures \result == weight;
public /*@ pure @*/int getWeight() {
    return weight;
}

/*@ also
@	requires kgs >= 0;
@	requires weight + kgs >= 0;
@ ensures weight == \old(weight + kgs);
@*/
public void addKgs(int kgs) {
    if (kgs >= 0) {
        weight += kgs;
    } else {
        throw new IllegalArgumentException();
    }
}



/*@ also
@	requires n != null && !n.equals("");
@	ensures n.equals(name) && weight == 0;
@*/
public Person(String n) {
    name = n; weight = 0;
}
}
