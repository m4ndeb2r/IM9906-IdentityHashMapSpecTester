package nl.ou.im9906;

import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.StreamCorruptedException;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.Assert.assertThrows;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

/**
 * Here we test an improved version of the orignal readObject method. It is extended with extra
 * input validation. The readObject code is copied into this class, instead of testing it in the
 * {@link java.util.IdentityHashMap}, and tested locally.
 */
public class ImprovedReadObjectTest {

    private ObjectInputStream objectInputStream;

    /**
     * Tests that the readObject method throws a StreamCorruptedException when the number
     * of allowed elements is exceeded. (This could never be the case in normal circumstances,
     * so the serialized object must be tampered with.
     * @throws IOException
     * @throws ClassNotFoundException
     */
    @Test(expected = StreamCorruptedException.class)
    public void testReadObjectThrowsStreamCorruptedExceptionWhenSizeTooBig()
            throws IOException, ClassNotFoundException {
        objectInputStream = mock(ObjectInputStream.class);
        when(objectInputStream.readInt()).thenReturn(MAXIMUM_CAPACITY + 1);
        readObject(objectInputStream);
    }

    private static final int MINIMUM_CAPACITY =  4;
    private static final int MAXIMUM_CAPACITY =  1 << 29;
    private static final Object NULL_KEY = new Object();
    private transient Object[] table;
    private transient int threshold;

    /**
     * Reconstitute the <tt>VerifiedIdentityHashMap</tt> instance from a stream (i.e.,
     * deserialize it). This is an improved version of the orignal readObject method.
     * It is extended with extra input validation.
     */
    private void readObject(java.io.ObjectInputStream s)
            throws java.io.IOException, ClassNotFoundException  {
        // Read in any hidden stuff
        s.defaultReadObject();

        // Read in size (number of Mappings)
        int size =  s.readInt();

        if (size > MAXIMUM_CAPACITY) {
            throw new java.io.StreamCorruptedException();
        }

        init(capacity((size * 4) / 3));

        // Read the keys and values, and put the mappings in the table
        for (int i =  0; i < size; i++) {
            java.lang.Object key =  (java.lang.Object) s.readObject();
            java.lang.Object value =  (java.lang.Object) s.readObject();
            putForCreate(key, value);
        }
    }

    /**
     * The put method for readObject.  It does not resize the table,
     * update modCount, etc.
     */
    private void putForCreate(java.lang.Object key, java.lang.Object value)
            throws IOException
    {
        java.lang.Object k =  (java.lang.Object)maskNull(key);
        Object[] tab =  table;
        int len =  tab.length;
        int i =  hash(k, len);

        Object item;
        while ( (item = tab[i]) != null) {
            if (item == k)
                throw new java.io.StreamCorruptedException();
            i = nextKeyIndex(i, len);
        }
        tab[i] = k;
        tab[i + 1] = value;
    }

    public static int hash(Object x, int length) {
        int h =  System.identityHashCode(x);
        // Multiply by -127, and left-shift to use least bit as part of hash
        return ((h << 1) - (h << 8)) & (length - 1);
    }

    private static int nextKeyIndex(int i, int len) {
        return (i + 2 < len ? i + 2 : 0);
    }

    public static Object maskNull(Object key) {
        return (key == null ? NULL_KEY : key);
    }

    private void init(int initCapacity) {
        assert (initCapacity & -initCapacity) == initCapacity; // power of 2
        assert initCapacity >= MINIMUM_CAPACITY;
        assert initCapacity <= MAXIMUM_CAPACITY;

        threshold = (initCapacity * 2) / 3;
        table = new Object[2 * initCapacity];
    }

    private int capacity(int expectedMaxSize) {
        int minCapacity = expectedMaxSize % 2 + (expectedMaxSize / 2) * 3; // Improved calculation
        int result;
        if (minCapacity > MAXIMUM_CAPACITY || minCapacity < 0) {
            result = MAXIMUM_CAPACITY;
        } else {
            result = MINIMUM_CAPACITY;
            while (result < minCapacity)
                result <<= 1;
        }
        return result;
    }
}
