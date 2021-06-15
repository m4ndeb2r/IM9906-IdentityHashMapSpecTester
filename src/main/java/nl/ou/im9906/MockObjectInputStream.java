package nl.ou.im9906;

import java.io.IOException;
import java.io.ObjectInputStream;

/**
 * Mock the {@link ObjectInputStream} class. Three methods of the overridden
 * {@link ObjectInputStream} are being mocked.
 */
class MockObjectInputStream extends ObjectInputStream {

    private final int numberOfMappings;

    protected MockObjectInputStream(int numberOfMappings) throws IOException, SecurityException {
        // This constructor enables readObjectOverride to be executed
        // when readObject is invoked.
        super();
        this.numberOfMappings = numberOfMappings;
    }

    /**
     * This is an empty implementation of {@link ObjectInputStream#defaultReadObject()},
     * because its workings are irrelevant to our case in point.
     */
    @Override
    public void defaultReadObject() {
        // Empty implementation
    }

    /**
     * We want to show that the overflow error occurs when a certain number of mappings
     * are present in the input stream.
     *
     * @return NUMBER_OF_MAPPINGS_IN_INPUTSTREAM
     */
    @Override
    public int readInt() {
        // Mock that inputStream contains a certain number of mappings
        return numberOfMappings;
    }

    /**
     * Because the {@link MockObjectInputStream} is created using the default constructor
     * of the super class, the {@link ObjectInputStream#enableOverride} is set to
     * {@code true}, meaning the non-final {@link ObjectInputStream#readObjectOverride()}
     * is called instead of the final {@link ObjectInputStream#readObject()}. We override
     * the {@link ObjectInputStream#readObjectOverride()} here by returning a trivial new
     * object every time it is invoked.
     *
     * @return a newly created object
     */
    @Override
    protected Object readObjectOverride() {
        return new Object();
    }
}
